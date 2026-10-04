package com.example.myapp

import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.res.ColorStateList
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.graphics.drawable.ColorDrawable
import android.graphics.drawable.RippleDrawable
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.text.InputType
import android.text.TextUtils
import android.util.LruCache
import android.util.TypedValue
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewConfiguration
import android.view.ViewGroup
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.InputMethodManager
import android.widget.AbsListView
import android.widget.ArrayAdapter
import android.widget.BaseAdapter
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.ListView
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.util.TreeSet

private const val NL: Byte = 10
private const val CR: Byte = 13
private val MP = ViewGroup.LayoutParams.MATCH_PARENT
private val WC = ViewGroup.LayoutParams.WRAP_CONTENT
private val COL_SELECTED = Color.parseColor("#FFD700")
private val COL_MAPPED = Color.parseColor("#90EE90")
private val COL_SEARCH = Color.parseColor("#ADD8E6")
private val COL_CURRENT = Color.parseColor("#00FF00")

private fun col(s: String): Int = Color.parseColor(s)

private fun humanSize(n: Long): String {
    if (n < 1024L) return "$n B"
    val kb = n / 1024.0
    if (kb < 1024.0) return String.format("%.1f KB", kb)
    val mb = kb / 1024.0
    if (mb < 1024.0) return String.format("%.1f MB", mb)
    return String.format("%.2f GB", mb / 1024.0)
}

// ════════════════════════════════════════════════════════════════════
//  LineSource : random-access line reader with sparse background index
//  (one checkpoint every 64 lines -> tiny memory even for GB files)
// ════════════════════════════════════════════════════════════════════
class LineSource(private val ctx: Context, val uri: Uri) {
    private var pfd: ParcelFileDescriptor? = null
    private var fis: FileInputStream? = null
    private var ch: FileChannel? = null
    var size: Long = 0L
    private var lastMod: Long = 0L

    @Volatile private var cp: LongArray = LongArray(4096)
    @Volatile private var cpCount: Int = 0
    @Volatile var lineCount: Int = 0
    @Volatile var done: Boolean = false
    @Volatile var error: String? = null
    @Volatile var bytesScanned: Long = 0L
    @Volatile private var cancelled: Boolean = false

    fun open(): Boolean {
        try {
            val p = ctx.contentResolver.openFileDescriptor(uri, "r")
            if (p == null) {
                error = "Cannot open file"
                done = true
                return false
            }
            pfd = p
            val st = FileInputStream(p.fileDescriptor)
            fis = st
            val c = st.channel
            ch = c
            size = c.size()
            if (size <= 0L) size = if (p.statSize > 0L) p.statSize else 0L
            lastMod = queryLastMod()
            return true
        } catch (e: Exception) {
            error = e.message ?: "Cannot open file"
            done = true
            return false
        }
    }

    private fun queryLastMod(): Long {
        try {
            val c = ctx.contentResolver.query(
                uri, arrayOf(DocumentsContract.Document.COLUMN_LAST_MODIFIED), null, null, null
            )
            if (c != null) {
                try {
                    if (c.moveToFirst() && !c.isNull(0)) return c.getLong(0)
                } finally {
                    c.close()
                }
            }
        } catch (e: Exception) {
        }
        return 0L
    }

    fun close() {
        cancelled = true
        try { ch?.close() } catch (e: Exception) { }
        try { fis?.close() } catch (e: Exception) { }
        try { pfd?.close() } catch (e: Exception) { }
        ch = null
    }

    // ---- index cache file ----
    private fun idxFile(): File = File(ctx.filesDir, "idx_" + uri.toString().hashCode().toString(16) + ".bin")

    fun deleteIndexFile() {
        try { idxFile().delete() } catch (e: Exception) { }
    }

    fun tryLoadIndex(): Boolean {
        try {
            val f = idxFile()
            if (!f.exists()) return false
            val d = DataInputStream(BufferedInputStream(FileInputStream(f), 1 shl 16))
            try {
                if (d.readInt() != 1) return false
                if (d.readLong() != size) return false
                if (d.readLong() != lastMod) return false
                val lc = d.readInt()
                val n = d.readInt()
                if (n <= 0 || n > 100000000) return false
                val arr = LongArray(if (n > 4096) n else 4096)
                for (i in 0 until n) arr[i] = d.readLong()
                cp = arr
                cpCount = n
                lineCount = lc
                bytesScanned = size
                done = true
            } finally {
                d.close()
            }
            return true
        } catch (e: Exception) {
            return false
        }
    }

    private fun saveIndex() {
        try {
            if (size < 4L * 1024L * 1024L) return
            val f = idxFile()
            val t = File(f.path + ".tmp")
            val d = DataOutputStream(BufferedOutputStream(FileOutputStream(t), 1 shl 16))
            try {
                d.writeInt(1)
                d.writeLong(size)
                d.writeLong(lastMod)
                d.writeInt(lineCount)
                val n = cpCount
                d.writeInt(n)
                val a = cp
                for (i in 0 until n) d.writeLong(a[i])
            } finally {
                d.close()
            }
            if (!t.renameTo(f)) t.delete()
        } catch (e: Exception) {
        }
    }

    // ---- background indexing ----
    fun startIndex() {
        val t = Thread(Runnable { indexRun() })
        t.priority = Thread.NORM_PRIORITY - 2
        t.isDaemon = true
        t.start()
    }

    private fun addCp(off: Long) {
        var a = cp
        val n = cpCount
        if (n >= a.size) {
            a = a.copyOf(a.size * 2)
            cp = a
        }
        a[n] = off
        cpCount = n + 1
    }

    private fun indexRun() {
        try {
            val c = ch
            if (c == null) {
                done = true
                return
            }
            val buf = ByteArray(1 shl 20)
            val bb = ByteBuffer.wrap(buf)
            var pos = 0L
            var nl = 0L
            var lastByte = -1
            addCp(0L)
            while (!cancelled) {
                bb.clear()
                val n = c.read(bb, pos)
                if (n <= 0) break
                var i = 0
                while (i < n) {
                    if (buf[i] == NL) {
                        nl++
                        if ((nl and 63L) == 0L) addCp(pos + i + 1)
                    }
                    i++
                }
                lastByte = buf[n - 1].toInt()
                pos += n
                lineCount = if (nl > Int.MAX_VALUE.toLong()) Int.MAX_VALUE else nl.toInt()
                bytesScanned = pos
            }
            if (!cancelled) {
                var total = nl
                if (pos > 0L && lastByte != 10) total++
                lineCount = if (total > Int.MAX_VALUE.toLong()) Int.MAX_VALUE else total.toInt()
                bytesScanned = size
                done = true
                saveIndex()
            }
        } catch (e: Exception) {
            if (!cancelled) {
                error = e.message ?: "Read error"
                done = true
            }
        }
    }

    private fun mk(b: ByteArray, len: Int, trunc: Boolean): String {
        var e = len
        if (!trunc && e > 0 && b[e - 1] == CR) e--
        val s = String(b, 0, e, Charsets.UTF_8)
        return if (trunc) s + "…" else s
    }

    /** Reads up to n lines starting at 0-based line `start`. Lines are cut at maxB bytes. */
    fun readLines(start: Int, n: Int, maxB: Int): Array<String> {
        val c = ch ?: return emptyArray()
        val total = lineCount
        if (n <= 0 || start < 0 || start >= total) return emptyArray()
        val block = start shr 6
        if (block >= cpCount) return emptyArray()
        val want = if (n < total - start) n else total - start
        var pos = cp[block]
        var skip = start - (block shl 6)
        val out = ArrayList<String>(want)
        val buf = ByteArray(32768)
        val bb = ByteBuffer.wrap(buf)
        var lb = ByteArray(256)
        var ll = 0
        var trunc = false
        try {
            loop@ while (out.size < want) {
                bb.clear()
                val r = c.read(bb, pos)
                if (r <= 0) break
                pos += r
                var i = 0
                while (i < r) {
                    val b = buf[i]
                    i++
                    if (b == NL) {
                        if (skip > 0) {
                            skip--
                        } else {
                            out.add(mk(lb, ll, trunc))
                            if (out.size >= want) break@loop
                        }
                        ll = 0
                        trunc = false
                    } else if (skip == 0) {
                        if (ll < maxB) {
                            if (ll == lb.size) {
                                val ns = if (lb.size * 2 < maxB) lb.size * 2 else maxB
                                lb = lb.copyOf(ns)
                            }
                            lb[ll] = b
                            ll++
                        } else {
                            trunc = true
                        }
                    }
                }
            }
            if (out.size < want && skip == 0 && (ll > 0 || trunc)) out.add(mk(lb, ll, trunc))
        } catch (e: Exception) {
        }
        return out.toTypedArray()
    }

    /** Case-insensitive search. Returns 0-based line index or -1. Wraps around. */
    fun find(term: String, from: Int, forward: Boolean, cancel: () -> Boolean): Int {
        val total = lineCount
        if (total <= 0) return -1
        val chunk = 256
        val start = ((from % total) + total) % total
        var scanned = 0
        if (forward) {
            var p = start
            while (scanned < total) {
                if (cancel()) return -1
                val n = if (chunk < total - p) chunk else total - p
                val arr = readLines(p, n, 1000000)
                if (arr.isEmpty()) return -1
                for (i in arr.indices) {
                    if (arr[i].contains(term, true)) return p + i
                }
                scanned += n
                p += n
                if (p >= total) p = 0
            }
        } else {
            var e = start + 1
            while (scanned < total) {
                if (cancel()) return -1
                val s0 = if (e - chunk > 0) e - chunk else 0
                val arr = readLines(s0, e - s0, 1000000)
                if (arr.isEmpty()) return -1
                var i = arr.size - 1
                while (i >= 0) {
                    if (arr[i].contains(term, true)) return s0 + i
                    i--
                }
                scanned += e - s0
                e = s0
                if (e <= 0) e = total
            }
        }
        return -1
    }
}

// ════════════════════════════════════════════════════════════════════
//  Panel : one file view (paged OR continuous scrolling)
// ════════════════════════════════════════════════════════════════════
class Panel(val act: MainActivity, val num: Int) {
    var src: LineSource? = null
    var uriStr: String? = null
    var fileName: String = ""
    var scrollMode: Boolean = false
    var page: Int = 1
    val selected = TreeSet<Int>()
    val mappedSet = HashSet<Int>()
    var searchTerm: String = ""
    var lastSearchTerm: String = ""
    var currentMatch: Int = -1
    var highlightLine: Int = -1
    var cursorLine: Int = -1
    var searchGen: Int = 0
    var winBase: Int = 0
    var winCount: Int = 0
    var maxBytes: Int = 1000000
    var pendingGlobal: Int = -1
    var pendingTop: Int = 0
    var userSeek: Boolean = false
    var hUser: Boolean = false
    var wrapMode: Boolean = false
    @Volatile var wantLo: Int = 0
    @Volatile var wantHi: Int = 0
    @Volatile var loadGen: Int = 0
    val loading = HashSet<Int>()
    val exec: java.util.concurrent.ExecutorService = java.util.concurrent.Executors.newSingleThreadExecutor { r ->
        val t = Thread(r)
        t.isDaemon = true
        t
    }
    var hOff: Int = 0
    var visChars: Int = 100
    var charW: Float = 10f
    var tx: Float = 0f
    var ty: Float = 0f
    var lastX: Float = 0f
    var panAcc: Float = 0f
    var hPan: Boolean = false
    val slop: Int = ViewConfiguration.get(act).scaledTouchSlop
    val cache = object : LruCache<Int, Array<String>>(12000000) {
        override fun sizeOf(key: Int, value: Array<String>): Int {
            var n = 0
            for (s in value) n += s.length + 16
            return if (n < 1) 1 else n
        }
    }

    val root = LinearLayout(act)
    val list = ListView(act)
    val seek = SeekBar(act)
    lateinit var modeBtn: Button
    lateinit var prevBtn: Button
    lateinit var nextBtn: Button
    lateinit var pageLbl: TextView
    lateinit var rangeLbl: TextView
    lateinit var gotoEt: EditText
    lateinit var findEt: EditText
    lateinit var jumpEt: EditText
    lateinit var wrapBtn: Button
    val hseek = SeekBar(act)

    val adapter = object : BaseAdapter() {
        override fun getCount(): Int = winCount
        override fun getItem(position: Int): Any? = null
        override fun getItemId(position: Int): Long = position.toLong()
        override fun getView(position: Int, convertView: View?, parent: ViewGroup?): View {
            val tv: TextView = (convertView as? TextView) ?: makeRow()
            val g = winBase + position
            val ln = g + 1
            val loaded = getLineOrNull(g)
            val line = loaded ?: ""
            val sb = StringBuilder()
            val ns = ln.toString()
            var k = ns.length
            while (k < 5) {
                sb.append(' ')
                k++
            }
            sb.append(ns).append(" | ")
            if (loaded == null) {
                sb.append("…")
            } else if (wrapMode) {
                if (line.length > 10000) {
                    sb.append(line, 0, 10000)
                    sb.append(" … (+").append(line.length - 10000).append(" chars: turn Wrap off and pan sideways)")
                } else {
                    sb.append(line)
                }
            } else if (hOff < line.length) {
                var en = hOff + visChars + 2
                if (en > line.length) en = line.length
                sb.append(line, hOff, en)
            }
            val wasWrap = tv.tag as? Boolean
            if (wasWrap == null || wasWrap != wrapMode) {
                tv.setSingleLine(!wrapMode)
                tv.tag = wrapMode
            }
            tv.text = sb
            tv.setTextSize(TypedValue.COMPLEX_UNIT_SP, act.fontSp)
            val color = if (ln == currentMatch || ln == highlightLine) COL_CURRENT
            else if (searchTerm.isNotEmpty() && line.contains(searchTerm, true)) COL_SEARCH
            else if (selected.contains(ln)) COL_SELECTED
            else if (mappedSet.contains(ln)) COL_MAPPED
            else Color.TRANSPARENT
            tv.setBackgroundColor(color)
            return tv
        }
    }

    private fun makeRow(): TextView {
        val tv = TextView(act)
        tv.typeface = Typeface.MONOSPACE
        tv.setTextSize(TypedValue.COMPLEX_UNIT_SP, act.fontSp)
        tv.setTextColor(Color.BLACK)
        tv.setSingleLine(true)
        tv.setPadding(act.dp(4), act.dp(1), act.dp(4), act.dp(1))
        tv.layoutParams = AbsListView.LayoutParams(MP, WC)
        return tv
    }

    private fun touchWant(b: Int) {
        if (b < wantLo || b > wantHi) {
            wantLo = b - 3
            wantHi = b + 3
        }
    }

    // Blocks are read on a background thread; the UI thread never touches the disk.
    private fun requestBlock(b: Int) {
        if (!loading.add(b)) return
        val s = src
        if (s == null) {
            loading.remove(b)
            return
        }
        val myGen = loadGen
        exec.execute(Runnable {
            if (myGen != loadGen || b < wantLo || b > wantHi) {
                act.runOnUiThread { loading.remove(b) }
                return@Runnable
            }
            val arr = s.readLines(b shl 6, 64, maxBytes)
            act.runOnUiThread {
                loading.remove(b)
                if (myGen == loadGen) {
                    if (arr.size == 64 || s.done) cache.put(b, arr)
                    adapter.notifyDataSetChanged()
                    updateHSeek()
                }
            }
        })
    }

    private fun block(b: Int): Array<String>? {
        val c = cache.get(b)
        if (c != null) return c
        requestBlock(b)
        return null
    }

    private fun getLineOrNull(g: Int): String? {
        val b = g shr 6
        touchWant(b)
        val arr = block(b) ?: return null
        val i = g and 63
        return if (i < arr.size) arr[i] else ""
    }

    private fun getLine(g: Int): String = getLineOrNull(g) ?: ""

    private fun hrow(bg: Int, vararg vs: View): HorizontalScrollView {
        val h = HorizontalScrollView(act)
        h.isHorizontalScrollBarEnabled = false
        h.setBackgroundColor(bg)
        val l = LinearLayout(act)
        l.orientation = LinearLayout.HORIZONTAL
        l.gravity = Gravity.CENTER_VERTICAL
        for (v in vs) l.addView(v)
        h.addView(l)
        return h
    }

    private fun onEnter(et: EditText, action: () -> Unit) {
        et.setOnEditorActionListener { _, actionId, ev ->
            val isAct = actionId == EditorInfo.IME_ACTION_GO || actionId == EditorInfo.IME_ACTION_SEARCH || actionId == EditorInfo.IME_ACTION_DONE
            val isEnter = ev != null && ev.keyCode == KeyEvent.KEYCODE_ENTER && ev.action == KeyEvent.ACTION_DOWN
            if (isAct || isEnter) {
                action()
                act.hideKb(et)
                true
            } else {
                false
            }
        }
    }

    init {
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(col("#DDDDDD"))

        val navColor = if (num == 1) col("#1976D2") else col("#E65100")
        val grey = col("#607D8B")

        val title = act.label("Text File $num", 14f, Color.BLACK)
        title.setTypeface(null, Typeface.BOLD)
        val openB = act.sbtn("Open", col("#455A64")) { act.pickFile(num) }
        val refB = act.sbtn("🔄 Refresh", grey) { reload() }
        modeBtn = act.sbtn("Mode: Paged", col("#8E24AA")) { toggleMode() }
        wrapBtn = act.sbtn("Wrap: Off", col("#00796B")) { toggleWrap() }
        val fm = act.sbtn("A-", grey) { act.changeFont(-1f) }
        val fp = act.sbtn("A+", grey) { act.changeFont(1f) }
        root.addView(hrow(col("#F0F0F0"), title, openB, refB, modeBtn, wrapBtn, fm, fp))

        gotoEt = act.edit(64, true, "line")
        gotoEt.imeOptions = EditorInfo.IME_ACTION_GO
        onEnter(gotoEt) { doGoto() }
        findEt = act.edit(110, false, "find")
        findEt.imeOptions = EditorInfo.IME_ACTION_SEARCH
        onEnter(findEt) { search(false) }
        val dn = act.sbtn("⬇", grey) { search(false) }
        val up = act.sbtn("⬆", grey) { search(true) }
        root.addView(
            hrow(
                col("#F0F0F0"),
                act.label("Go to:", 12f, Color.BLACK), gotoEt,
                act.label("Find:", 12f, Color.BLACK), findEt, dn, up
            )
        )

        prevBtn = act.sbtn("◀ Prev", navColor) { prevPage() }
        pageLbl = act.label("Page 1/1", 12f, Color.BLACK)
        pageLbl.setTypeface(null, Typeface.BOLD)
        nextBtn = act.sbtn("Next ▶", navColor) { nextPage() }
        jumpEt = act.edit(56, true, "pg")
        jumpEt.imeOptions = EditorInfo.IME_ACTION_GO
        onEnter(jumpEt) { doJump() }
        val goB = act.sbtn("Go", col("#455A64")) { doJump(); act.hideKb(jumpEt) }
        rangeLbl = act.label("", 12f, col("#444444"))
        root.addView(
            hrow(
                col("#DCE8F5"),
                prevBtn, pageLbl, nextBtn,
                act.label(" Jump:", 12f, Color.BLACK), jumpEt, goB, rangeLbl
            )
        )

        seek.visibility = View.GONE
        seek.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {
                if (fromUser) {
                    pendingGlobal = -1
                    list.setSelectionFromTop(progress, 0)
                }
            }

            override fun onStartTrackingTouch(sb: SeekBar?) {
                userSeek = true
            }

            override fun onStopTrackingTouch(sb: SeekBar?) {
                userSeek = false
                act.saveView()
            }
        })
        root.addView(seek, LinearLayout.LayoutParams(MP, WC))

        list.divider = null
        list.dividerHeight = 0
        list.overScrollMode = View.OVER_SCROLL_NEVER
        list.setSelector(ColorDrawable(Color.TRANSPARENT))
        list.cacheColorHint = Color.TRANSPARENT
        list.isVerticalScrollBarEnabled = true
        list.adapter = adapter
        list.setBackgroundColor(Color.WHITE)
        list.setOnItemClickListener { _, _, pos, _ -> onRowClick(winBase + pos + 1) }
        list.setOnItemLongClickListener { _, _, pos, _ ->
            copyLine(winBase + pos + 1)
            true
        }
        list.setOnTouchListener { _, ev ->
            act.lastPanel = this
            pendingGlobal = -1
            var consumed = false
            val a = ev.actionMasked
            if (a == MotionEvent.ACTION_DOWN) {
                act.dropEditFocus()
                tx = ev.x
                ty = ev.y
                lastX = ev.x
                panAcc = 0f
                hPan = false
            } else if (a == MotionEvent.ACTION_MOVE) {
                if (!wrapMode) {
                    if (!hPan) {
                        val dx = ev.x - tx
                        val dy = ev.y - ty
                        if (Math.abs(dx) > slop && Math.abs(dx) > Math.abs(dy) * 2f) {
                            hPan = true
                            val c = MotionEvent.obtain(ev)
                            c.action = MotionEvent.ACTION_CANCEL
                            list.onTouchEvent(c)
                            c.recycle()
                            lastX = ev.x
                        }
                    }
                    if (hPan) {
                        panAcc += (lastX - ev.x) / charW
                        lastX = ev.x
                        val whole = panAcc.toInt()
                        if (whole != 0) {
                            panByChars(whole)
                            panAcc -= whole.toFloat()
                        }
                        consumed = true
                    }
                }
            } else if (a == MotionEvent.ACTION_UP || a == MotionEvent.ACTION_CANCEL) {
                if (hPan) {
                    consumed = true
                    hPan = false
                    panAcc = 0f
                }
            }
            consumed
        }
        list.setOnScrollListener(object : AbsListView.OnScrollListener {
            override fun onScrollStateChanged(view: AbsListView?, scrollState: Int) {
                if (scrollState == AbsListView.OnScrollListener.SCROLL_STATE_IDLE) act.saveView()
            }

            override fun onScroll(view: AbsListView?, firstVisibleItem: Int, visibleItemCount: Int, totalItemCount: Int) {
                updateRange()
                updateHSeek()
            }
        })
        root.addView(list, LinearLayout.LayoutParams(MP, 0, 1f))

        hseek.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {
                if (fromUser) applyHOff(progress)
            }

            override fun onStartTrackingTouch(sb: SeekBar?) {
                hUser = true
            }

            override fun onStopTrackingTouch(sb: SeekBar?) {
                hUser = false
            }
        })
        list.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ ->
            val nv = computeVis()
            if (nv != visChars) {
                visChars = nv
                list.post {
                    adapter.notifyDataSetChanged()
                    updateHSeek()
                }
            }
        }
        root.addView(hseek, LinearLayout.LayoutParams(MP, WC))

        applyFont()
        applyModeUi()
        applyWrapUi()
    }

    // ---------------- font / width ----------------
    fun applyFont() {
        val p = Paint()
        p.typeface = Typeface.MONOSPACE
        p.textSize = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_SP, act.fontSp, act.resources.displayMetrics)
        var cw = p.measureText("0")
        if (cw < 1f) cw = 1f
        charW = cw
        visChars = computeVis()
        cache.evictAll()
        adapter.notifyDataSetChanged()
        updateHSeek()
    }

    fun computeVis(): Int {
        val w = list.width
        if (w <= 0) return 100
        val v = ((w - act.dp(8)) / charW).toInt() - 8
        return if (v < 10) 10 else v
    }

    fun maxHOff(): Int {
        var m = 0
        val f = list.firstVisiblePosition
        val l = list.lastVisiblePosition
        var pos = f
        while (pos <= l && pos < winCount) {
            val len = getLine(winBase + pos).length
            if (len > m) m = len
            pos++
        }
        val mx = m - visChars
        return if (mx < 0) 0 else mx
    }

    fun applyHOff(v: Int) {
        val mx = maxHOff()
        var n = v
        if (n > mx) n = mx
        if (n < 0) n = 0
        if (n != hOff) {
            hOff = n
            adapter.notifyDataSetChanged()
        }
        if (!hUser && hseek.progress != n) hseek.progress = n
    }

    fun panByChars(d: Int) {
        if (wrapMode) return
        applyHOff(hOff + d)
    }

    fun updateHSeek() {
        if (wrapMode) return
        val mx = maxHOff()
        val smx = if (mx < 1) 1 else mx
        if (hseek.max != smx) hseek.max = smx
        val shown = if (hOff < mx) hOff else mx
        if (!hUser && hseek.progress != shown) hseek.progress = shown
    }

    fun applyWrapUi() {
        wrapBtn.text = if (wrapMode) "Wrap: On" else "Wrap: Off"
        hseek.visibility = if (wrapMode) View.GONE else View.VISIBLE
        adapter.notifyDataSetChanged()
        updateHSeek()
    }

    fun toggleWrap() {
        val f = list.firstVisiblePosition
        wrapMode = !wrapMode
        hOff = 0
        applyWrapUi()
        list.post { list.setSelectionFromTop(f, 0) }
        act.saveView()
    }

    fun redraw() {
        adapter.notifyDataSetChanged()
    }

    // ---------------- loading ----------------
    fun loadFile(u: String?, restoreGlobal: Int, restoreTop: Int, force: Boolean) {
        reloadSrc?.close()
        reloadSrc = null
        src?.close()
        src = null
        loadGen++
        loading.clear()
        cache.evictAll()
        uriStr = u
        winBase = 0
        winCount = 0
        pendingGlobal = restoreGlobal
        pendingTop = restoreTop
        if (restoreGlobal >= 0) {
            savedG = restoreGlobal
            savedT = restoreTop
        }
        if (u == null) {
            fileName = ""
            refreshWindow()
            act.updateFileLabels()
            return
        }
        val uri = Uri.parse(u)
        fileName = act.displayName(uri)
        val s = LineSource(act, uri)
        src = s
        if (s.open()) {
            if (force) s.deleteIndexFile()
            if (force || !s.tryLoadIndex()) s.startIndex()
        } else {
            act.toast("File $num: " + (s.error ?: "cannot open"))
        }
        refreshWindow()
        tryRestore()
        act.ensureTicker()
        act.updateFileLabels()
    }

    // Refresh: the old text stays on screen while the file is re-indexed in the
    // background; then the new source is swapped in at the CURRENT scroll position.
    var reloadSrc: LineSource? = null

    fun reload() {
        val u = uriStr ?: return
        reloadSrc?.close()
        reloadSrc = null
        val ns = LineSource(act, Uri.parse(u))
        if (!ns.open()) {
            act.toast("File $num: " + (ns.error ?: "cannot open"))
            ns.close()
            return
        }
        ns.deleteIndexFile()
        ns.startIndex()
        reloadSrc = ns
        act.ensureTicker()
    }

    private fun checkReload() {
        val rs = reloadSrc ?: return
        if (rs.error != null) {
            act.toast("File $num: " + (rs.error ?: "refresh failed"))
            rs.close()
            reloadSrc = null
            return
        }
        val g0 = firstGlobal()
        val ready = rs.done || rs.lineCount > g0 + act.linesPerPage + 500
        if (!ready) return
        var g = g0
        val t = firstTop()
        src?.close()
        src = rs
        reloadSrc = null
        loadGen++
        loading.clear()
        cache.evictAll()
        pendingGlobal = -1
        if (rs.lineCount > 0 && g >= rs.lineCount) g = rs.lineCount - 1
        if (g < 0) g = 0
        if (!scrollMode) page = g / act.linesPerPage + 1
        refreshWindow()
        val idx = g - winBase
        list.setSelectionFromTop(if (idx < 0) 0 else idx, t)
        list.post { list.setSelectionFromTop(if (idx < 0) 0 else idx, t) }
        act.updateFileLabels()
    }

    fun tick() {
        checkReload()
        val s = src ?: return
        tryRestore()
        refreshWindow(false)
        if (s.done && pendingGlobal >= 0) pendingGlobal = -1
    }

    private fun tryRestore() {
        if (pendingGlobal < 0) return
        val s = src ?: return
        if (pendingGlobal < s.lineCount) {
            val g = pendingGlobal
            val top = pendingTop
            pendingGlobal = -1
            if (!scrollMode) page = g / act.linesPerPage + 1
            refreshWindow()
            val idx = g - winBase
            list.post { list.setSelectionFromTop(if (idx < 0) 0 else idx, top) }
        } else if (s.done) {
            pendingGlobal = -1
        }
    }

    // ---------------- window / pagination ----------------
    fun totalPages(): Int {
        val t = (src?.lineCount ?: 0).toLong()
        val l = act.linesPerPage.toLong()
        val p = ((t + l - 1L) / l).toInt()
        return if (p < 1) 1 else p
    }

    fun refreshWindow(force: Boolean = true) {
        val s = src
        val total = s?.lineCount ?: 0
        val lpp = act.linesPerPage
        var nb = 0
        var nc = total
        if (!scrollMode) {
            val tp = totalPages()
            if (s != null && s.done && page > tp) page = tp
            if (page < 1) page = 1
            nb = (page - 1) * lpp
            nc = total - nb
            if (nc > lpp) nc = lpp
            if (nc < 0) nc = 0
        }
        val changed = nb != winBase || nc != winCount
        winBase = nb
        winCount = nc
        if (changed || force) adapter.notifyDataSetChanged()
        updatePagination()
        updateRange()
    }

    private fun setEn(b: Button, en: Boolean) {
        b.isEnabled = en
        b.alpha = if (en) 1f else 0.4f
    }

    fun updatePagination() {
        if (scrollMode) {
            pageLbl.text = "Scroll"
            setEn(prevBtn, true)
            setEn(nextBtn, true)
        } else {
            val tp = totalPages()
            val plus = if (src?.done == false) "+" else ""
            pageLbl.text = "Page $page/$tp$plus"
            setEn(prevBtn, page > 1)
            setEn(nextBtn, page < tp)
        }
    }

    fun updateRange() {
        if (winCount <= 0) {
            rangeLbl.text = ""
            return
        }
        val total = src?.lineCount ?: 0
        if (scrollMode) {
            val f = list.firstVisiblePosition
            var l = list.lastVisiblePosition
            if (l < f) l = f
            val txt = "Lines ${winBase + f + 1}–${winBase + l + 1} / $total"
            if (rangeLbl.text.toString() != txt) rangeLbl.text = txt
            if (!userSeek) {
                val mx = if (winCount - 1 > 1) winCount - 1 else 1
                if (seek.max != mx) seek.max = mx
                if (seek.progress != f) seek.progress = f
            }
        } else {
            rangeLbl.text = "Lines ${winBase + 1}–${winBase + winCount}"
        }
    }

    // Last known on-screen position. A hidden (single-file mode) or not-yet-laid-out
    // list reports position 0, so we keep the last real value instead of overwriting it.
    var savedG: Int = -1
    var savedT: Int = 0

    private fun listLive(): Boolean = list.isShown && list.childCount > 0

    fun firstGlobal(): Int {
        if (pendingGlobal >= 0) return pendingGlobal
        if (listLive()) {
            savedG = winBase + list.firstVisiblePosition
            val c = list.getChildAt(0)
            savedT = if (c != null) c.top else 0
            return savedG
        }
        if (savedG >= 0) return savedG
        return winBase + list.firstVisiblePosition
    }

    fun firstTop(): Int {
        if (pendingGlobal >= 0) return pendingTop
        if (listLive()) {
            val c = list.getChildAt(0)
            savedT = if (c != null) c.top else 0
            savedG = winBase + list.firstVisiblePosition
            return savedT
        }
        if (savedG >= 0) return savedT
        return 0
    }

    // Re-apply the remembered position (used when a hidden panel becomes visible again).
    fun reapplyPosition() {
        if (pendingGlobal >= 0 || savedG < 0) return
        val g = savedG
        val tp = savedT
        list.post {
            val idx = g - winBase
            if (idx >= 0 && idx < winCount) list.setSelectionFromTop(idx, tp)
        }
    }

    fun applyModeUi() {
        modeBtn.text = if (scrollMode) "Mode: Scroll" else "Mode: Paged"
        seek.visibility = if (scrollMode) View.VISIBLE else View.GONE
    }

    fun toggleMode() {
        val g = firstGlobal()
        pendingGlobal = -1
        scrollMode = !scrollMode
        applyModeUi()
        if (scrollMode) {
            refreshWindow()
            list.post { list.setSelectionFromTop(g, 0) }
        } else {
            page = g / act.linesPerPage + 1
            refreshWindow()
            val idx = g - winBase
            list.post { list.setSelectionFromTop(if (idx < 0) 0 else idx, 0) }
        }
        act.saveView()
    }

    fun nextPage() {
        if (scrollMode) scrollScreen(1) else changePage(1)
    }

    fun prevPage() {
        if (scrollMode) scrollScreen(-1) else changePage(-1)
    }

    private fun scrollScreen(dir: Int) {
        pendingGlobal = -1
        val f = list.firstVisiblePosition
        var vis = list.lastVisiblePosition - f
        if (vis < 1) vis = 1
        var t = f + dir * vis
        val mx = if (winCount - 1 > 0) winCount - 1 else 0
        if (t < 0) t = 0
        if (t > mx) t = mx
        list.setSelectionFromTop(t, 0)
    }

    private fun changePage(d: Int) {
        val tp = totalPages()
        var np = page + d
        if (np < 1) np = 1
        if (np > tp) np = tp
        if (np == page) return
        page = np
        pendingGlobal = -1
        refreshWindow()
        list.setSelection(0)
        act.saveView()
    }

    private fun doJump() {
        val v = jumpEt.text.toString().trim().toIntOrNull()
        val tp = totalPages()
        if (v == null || v < 1 || v > tp) {
            act.toast("Page must be between 1 and $tp.")
            return
        }
        jumpEt.setText("")
        pendingGlobal = -1
        if (scrollMode) {
            list.setSelectionFromTop((v - 1) * act.linesPerPage, 0)
        } else {
            page = v
            refreshWindow()
            list.setSelection(0)
        }
        act.saveView()
    }

    // ---------------- goto / search ----------------
    private fun doGoto() {
        val total = src?.lineCount ?: 0
        val v = gotoEt.text.toString().trim().toIntOrNull()
        if (v == null || v < 1 || v > total) {
            act.toast("Enter a line number between 1 and $total.")
            return
        }
        gotoEt.setText("")
        gotoLine(v, true)
    }

    fun gotoLine(ln: Int, highlight: Boolean) {
        val total = src?.lineCount ?: 0
        if (ln < 1 || ln > total) return
        pendingGlobal = -1
        if (!scrollMode) {
            page = (ln - 1) / act.linesPerPage + 1
            refreshWindow()
        }
        val idx = ln - 1 - winBase
        list.post { list.setSelectionFromTop(if (idx < 0) 0 else idx, act.dp(60)) }
        if (highlight) {
            highlightLine = ln
            adapter.notifyDataSetChanged()
            act.handler.postDelayed({
                if (highlightLine == ln) {
                    highlightLine = -1
                    adapter.notifyDataSetChanged()
                }
            }, 2000)
        }
        act.saveView()
    }

    fun search(backward: Boolean) {
        val term = findEt.text.toString().trim()
        if (term.isEmpty()) {
            searchTerm = ""
            lastSearchTerm = ""
            currentMatch = -1
            searchGen++
            adapter.notifyDataSetChanged()
            return
        }
        val s = src ?: return
        searchTerm = term
        val gen = ++searchGen
        val from: Int
        if (term == lastSearchTerm && currentMatch > 0) {
            from = if (backward) currentMatch - 2 else currentMatch
        } else {
            val g = firstGlobal()
            from = if (backward) g - 1 else g
        }
        adapter.notifyDataSetChanged()
        rangeLbl.text = "Searching…"
        val fwd = !backward
        val th = Thread(Runnable {
            val r = s.find(term, from, fwd) { gen != searchGen }
            act.runOnUiThread {
                if (gen == searchGen) onFound(term, r)
            }
        })
        th.isDaemon = true
        th.start()
    }

    private fun onFound(term: String, r: Int) {
        if (r < 0) {
            currentMatch = -1
            act.toast("'$term' not found")
            adapter.notifyDataSetChanged()
            updateRange()
        } else {
            currentMatch = r + 1
            lastSearchTerm = term
            gotoLine(r + 1, false)
            adapter.notifyDataSetChanged()
        }
    }

    // ---------------- clicks / copy ----------------
    fun onRowClick(ln: Int) {
        cursorLine = ln
        act.lastPanel = this
        if (act.phase == num) {
            if (!selected.remove(ln)) selected.add(ln)
            act.updateSelectionLabel()
        }
        adapter.notifyDataSetChanged()
    }

    fun copyLine(ln: Int) {
        val s = src ?: return
        val th = Thread(Runnable {
            val a = s.readLines(ln - 1, 1, 8000000)
            act.runOnUiThread {
                if (a.isNotEmpty()) {
                    try {
                        val cm = act.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
                        cm.setPrimaryClip(ClipData.newPlainText("line", a[0]))
                        act.toast("Copied line $ln")
                    } catch (e: Exception) {
                        act.toast("Line too large for the clipboard")
                    }
                }
            }
        })
        th.isDaemon = true
        th.start()
    }

    fun copyCursor() {
        if (cursorLine > 0) copyLine(cursorLine) else act.toast("Tap a line first")
    }
}

// ════════════════════════════════════════════════════════════════════
//  MainActivity
// ════════════════════════════════════════════════════════════════════
class MainActivity : Activity() {
    lateinit var prefs: SharedPreferences
    val handler = Handler(Looper.getMainLooper())
    lateinit var p1: Panel
    lateinit var p2: Panel
    lateinit var lastPanel: Panel
    lateinit var rootLayout: LinearLayout
    private lateinit var container: LinearLayout
    private lateinit var file1Label: TextView
    private lateinit var file2Label: TextView
    private lateinit var phaseTv: TextView
    private lateinit var selectionTv: TextView
    private lateinit var sw1: Button
    private lateinit var sw2: Button

    var fontSp: Float = 11f
    var linesPerPage: Int = 30
    var layoutMode: Int = 0
    var phase: Int = 1
    private var ready = false
    private var tickerOn = false

    val maps1 = ArrayList<IntArray>()
    val maps2 = ArrayList<IntArray>()
    val combined = ArrayList<String>()

    private val tickRunnable = object : Runnable {
        override fun run() {
            var any = false
            for (p in listOf(p1, p2)) {
                p.tick()
                val s = p.src
                if (s != null && !s.done) any = true
                if (p.reloadSrc != null) any = true
            }
            updateFileLabels()
            if (any) handler.postDelayed(this, 300) else tickerOn = false
        }
    }

    // ---------------- small helpers ----------------
    fun dp(v: Int): Int = (v * resources.displayMetrics.density + 0.5f).toInt()

    fun toast(s: String) {
        Toast.makeText(this, s, Toast.LENGTH_SHORT).show()
    }

    fun panel(n: Int): Panel = if (n == 1) p1 else p2

    fun maps(n: Int): ArrayList<IntArray> = if (n == 1) maps1 else maps2

    private fun ripple(color: Int): RippleDrawable =
        RippleDrawable(ColorStateList.valueOf(0x66FFFFFF), ColorDrawable(color), null)

    fun label(text: String, sizeSp: Float, color: Int): TextView {
        val t = TextView(this)
        t.text = text
        t.textSize = sizeSp
        t.setTextColor(color)
        t.setPadding(dp(4), dp(2), dp(4), dp(2))
        return t
    }

    fun sbtn(text: String, color: Int, cmd: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.textSize = 11f
        b.setTextColor(Color.WHITE)
        b.minWidth = 0
        b.minimumWidth = 0
        b.minHeight = 0
        b.minimumHeight = 0
        b.setPadding(dp(8), 0, dp(8), 0)
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.stateListAnimator = null
        b.background = ripple(color)
        b.setOnClickListener { cmd() }
        val lp = LinearLayout.LayoutParams(WC, dp(34))
        lp.setMargins(dp(2), dp(1), dp(2), dp(1))
        b.layoutParams = lp
        return b
    }

    private fun toolBtn(text: String, color: Int, cmd: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.textSize = 11f
        b.setTextColor(Color.WHITE)
        b.minWidth = 0
        b.minimumWidth = 0
        b.minHeight = 0
        b.minimumHeight = dp(44)
        b.setPadding(dp(2), 0, dp(2), 0)
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.stateListAnimator = null
        b.background = ripple(color)
        b.setOnClickListener { cmd() }
        val lp = LinearLayout.LayoutParams(0, WC, 1f)
        lp.setMargins(dp(2), dp(2), dp(2), dp(2))
        b.layoutParams = lp
        return b
    }

    fun edit(widthDp: Int, numeric: Boolean, hint: String): EditText {
        val e = EditText(this)
        e.inputType = if (numeric) InputType.TYPE_CLASS_NUMBER else InputType.TYPE_CLASS_TEXT
        e.textSize = 12f
        e.setTextColor(Color.BLACK)
        e.setBackgroundColor(Color.WHITE)
        e.setPadding(dp(4), dp(4), dp(4), dp(4))
        e.hint = hint
        e.setHintTextColor(Color.GRAY)
        val lp = LinearLayout.LayoutParams(dp(widthDp), dp(34))
        lp.setMargins(dp(2), dp(1), dp(2), dp(1))
        e.layoutParams = lp
        return e
    }

    fun hideKb(v: View) {
        val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        imm.hideSoftInputFromWindow(v.windowToken, 0)
        v.clearFocus()
        rootLayout.requestFocus()
    }

    fun dropEditFocus() {
        val f = currentFocus
        if (f is EditText) hideKb(f)
    }

    fun displayName(u: Uri): String {
        try {
            val c = contentResolver.query(u, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)
            if (c != null) {
                try {
                    if (c.moveToFirst()) {
                        val n = c.getString(0)
                        if (n != null) return n
                    }
                } finally {
                    c.close()
                }
            }
        } catch (e: Exception) {
        }
        return u.lastPathSegment ?: "file"
    }

    private fun fmt(n: Int): String = String.format("%,d", n)

    fun confirm(msg: String, yes: () -> Unit) {
        AlertDialog.Builder(this)
            .setMessage(msg)
            .setPositiveButton("Yes") { _, _ -> yes() }
            .setNegativeButton("No", null)
            .show()
    }

    // ---------------- lifecycle ----------------
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        prefs = getSharedPreferences("seqmapper", Context.MODE_PRIVATE)
        fontSp = prefs.getFloat("font", 11f)
        linesPerPage = prefs.getInt("lpp", 30)
        layoutMode = prefs.getInt("layout", 0)
        phase = prefs.getInt("phase", 1)

        p1 = Panel(this, 1)
        p2 = Panel(this, 2)
        lastPanel = p1

        rootLayout = LinearLayout(this)
        rootLayout.orientation = LinearLayout.VERTICAL
        rootLayout.setBackgroundColor(col("#F0F0F0"))
        rootLayout.isFocusable = true
        rootLayout.isFocusableInTouchMode = true

        file1Label = label("File 1: Not selected", 11f, Color.BLACK)
        file2Label = label("File 2: Not selected", 11f, Color.BLACK)
        for (t in listOf(file1Label, file2Label)) {
            t.setSingleLine(true)
            t.ellipsize = TextUtils.TruncateAt.END
            rootLayout.addView(t, LinearLayout.LayoutParams(MP, WC))
        }

        sw1 = toolBtn("Switch to\nFile 1", col("#2196F3")) { switchTo(1) }
        sw2 = toolBtn("Switch to\nFile 2", col("#2196F3")) { switchTo(2) }

        val row1 = LinearLayout(this)
        row1.orientation = LinearLayout.HORIZONTAL
        row1.addView(toolBtn("Save (S)", col("#4CAF50")) { saveMapping() })
        row1.addView(toolBtn("Clear", col("#FF9800")) { clearSelection() })
        row1.addView(sw1)
        row1.addView(sw2)
        row1.addView(toolBtn("Combine", col("#673AB7")) { combine() })
        rootLayout.addView(row1, LinearLayout.LayoutParams(MP, WC))

        val row2 = LinearLayout(this)
        row2.orientation = LinearLayout.HORIZONTAL
        row2.addView(toolBtn("View\nMappings", col("#9C27B0")) { showMappings() })
        row2.addView(toolBtn("Export", col("#009688")) { exportCombined() })
        row2.addView(toolBtn("Duplicates", col("#FF5722")) { showDuplicates() })
        row2.addView(toolBtn("Lines/Page", col("#607D8B")) { setLinesPerPage() })
        row2.addView(toolBtn("Layout", col("#795548")) { cycleLayout() })
        rootLayout.addView(row2, LinearLayout.LayoutParams(MP, WC))

        phaseTv = label("Phase: Mapping File 1", 13f, col("#2196F3"))
        phaseTv.setTypeface(null, Typeface.BOLD)
        rootLayout.addView(phaseTv, LinearLayout.LayoutParams(MP, WC))
        selectionTv = label("File 1 Selection: []", 12f, Color.BLACK)
        selectionTv.maxLines = 2
        selectionTv.ellipsize = TextUtils.TruncateAt.END
        rootLayout.addView(selectionTv, LinearLayout.LayoutParams(MP, WC))

        container = LinearLayout(this)
        container.addView(p1.root)
        container.addView(p2.root)
        rootLayout.addView(container, LinearLayout.LayoutParams(MP, 0, 1f))

        setContentView(rootLayout)
        rootLayout.requestFocus()

        loadState()
        applyLayout()
        updateUi()
        updateFileLabels()
        ready = true

        if (p1.uriStr == null || p2.uriStr == null) askFiles()
    }

    override fun onPause() {
        super.onPause()
        saveView()
        saveMaps()
    }

    override fun onDestroy() {
        super.onDestroy()
        p1.src?.close()
        p2.src?.close()
        p1.reloadSrc?.close()
        p2.reloadSrc?.close()
    }

    // ---------------- state ----------------
    private fun encMaps(m: List<IntArray>): String {
        val sb = StringBuilder()
        for (i in m.indices) {
            if (i > 0) sb.append(';')
            val a = m[i]
            for (j in a.indices) {
                if (j > 0) sb.append(',')
                sb.append(a[j])
            }
        }
        return sb.toString()
    }

    private fun decMaps(s: String): List<IntArray> {
        val out = ArrayList<IntArray>()
        if (s.isEmpty()) return out
        for (part in s.split(";")) {
            val nums = ArrayList<Int>()
            for (x in part.split(",")) {
                val v = x.trim().toIntOrNull()
                if (v != null) nums.add(v)
            }
            if (nums.isNotEmpty()) out.add(nums.toIntArray())
        }
        return out
    }

    fun saveMaps() {
        if (!ready) return
        val e = prefs.edit()
        e.putString("m1", encMaps(maps1))
        e.putString("m2", encMaps(maps2))
        e.putString("comb", combined.joinToString("\n"))
        e.apply()
    }

    fun saveView() {
        if (!ready) return
        val e = prefs.edit()
        e.putFloat("font", fontSp)
        e.putInt("lpp", linesPerPage)
        e.putInt("layout", layoutMode)
        e.putInt("phase", phase)
        for (p in listOf(p1, p2)) {
            val n = p.num
            e.putString("uri$n", p.uriStr)
            e.putBoolean("scroll$n", p.scrollMode)
            e.putBoolean("wrap$n", p.wrapMode)
            e.putInt("hoff$n", p.hOff)
            e.putInt("pos$n", p.firstGlobal())
            e.putInt("top$n", p.firstTop())
            e.putString("sel$n", p.selected.joinToString(","))
            e.putInt("cur$n", p.cursorLine)
        }
        e.apply()
    }

    private fun loadState() {
        maps1.addAll(decMaps(prefs.getString("m1", "") ?: ""))
        maps2.addAll(decMaps(prefs.getString("m2", "") ?: ""))
        val cs = prefs.getString("comb", "") ?: ""
        for (x in cs.split("\n")) if (x.isNotEmpty()) combined.add(x)
        for (p in listOf(p1, p2)) {
            val n = p.num
            p.scrollMode = prefs.getBoolean("scroll$n", false)
            p.wrapMode = prefs.getBoolean("wrap$n", false)
            p.hOff = prefs.getInt("hoff$n", 0)
            val ss = prefs.getString("sel$n", "") ?: ""
            for (x in ss.split(",")) {
                val v = x.trim().toIntOrNull()
                if (v != null) p.selected.add(v)
            }
            p.cursorLine = prefs.getInt("cur$n", -1)
            p.applyModeUi()
            p.applyWrapUi()
        }
        rebuildMapped()
        for (p in listOf(p1, p2)) {
            val n = p.num
            p.loadFile(prefs.getString("uri$n", null), prefs.getInt("pos$n", 0), prefs.getInt("top$n", 0), false)
        }
    }

    private fun rebuildMapped() {
        for (n in 1..2) {
            val p = panel(n)
            p.mappedSet.clear()
            for (m in maps(n)) for (x in m) p.mappedSet.add(x)
        }
    }

    // ---------------- ticker / labels ----------------
    fun ensureTicker() {
        if (!tickerOn) {
            tickerOn = true
            handler.postDelayed(tickRunnable, 300)
        }
    }

    private fun labelText(p: Panel): String {
        if (p.uriStr == null) return "File ${p.num}: Not selected"
        val s = p.src
        val st: String = if (s == null) {
            ""
        } else if (s.error != null) {
            " — error: ${s.error}"
        } else if (s.done) {
            " — ${fmt(s.lineCount)} lines · ${humanSize(s.size)}"
        } else {
            val pct = if (s.size > 0L) (s.bytesScanned * 100L / s.size).toInt() else 0
            " — indexing $pct% · ${fmt(s.lineCount)} lines so far"
        }
        return "File ${p.num}: ${p.fileName}$st"
    }

    fun updateFileLabels() {
        if (!ready && !::file2Label.isInitialized) return
        file1Label.text = labelText(p1)
        file2Label.text = labelText(p2)
    }

    // ---------------- UI state ----------------
    private fun setEn(b: Button, en: Boolean) {
        b.isEnabled = en
        b.alpha = if (en) 1f else 0.4f
    }

    fun updateUi() {
        phaseTv.text = "Phase: Mapping File $phase  (${maps(phase).size} saved)"
        phaseTv.setTextColor(if (phase == 1) col("#2196F3") else col("#FF9800"))
        for (p in listOf(p1, p2)) {
            p.list.setBackgroundColor(if (p.num == phase) Color.WHITE else col("#F0F0F0"))
            p.redraw()
        }
        setEn(sw1, phase != 1 || (layoutMode >= 2 && layoutMode != 2))
        setEn(sw2, phase != 2 || (layoutMode >= 2 && layoutMode != 3))
        updateSelectionLabel()
    }

    fun updateSelectionLabel() {
        val p = panel(phase)
        var s = p.selected.joinToString(",")
        if (s.isEmpty()) s = "[]"
        selectionTv.text = "File $phase Selection: $s"
    }

    fun applyLayout() {
        container.orientation = if (layoutMode == 1) LinearLayout.VERTICAL else LinearLayout.HORIZONTAL
        for (p in listOf(p1, p2)) {
            val lp = if (layoutMode == 1) LinearLayout.LayoutParams(MP, 0, 1f) else LinearLayout.LayoutParams(0, MP, 1f)
            lp.setMargins(dp(3), dp(3), dp(3), dp(3))
            p.root.layoutParams = lp
        }
        for (p in listOf(p1, p2)) {
            p.firstGlobal()
            val wasHidden = p.root.visibility != View.VISIBLE
            val hide = (p.num == 1 && layoutMode == 3) || (p.num == 2 && layoutMode == 2)
            p.root.visibility = if (hide) View.GONE else View.VISIBLE
            if (wasHidden && !hide) p.reapplyPosition()
        }
    }

    private fun cycleLayout() {
        layoutMode = (layoutMode + 1) % 4
        applyLayout()
        updateUi()
        val names = arrayOf("Two panels: side by side", "Two panels: stacked", "File 1 only", "File 2 only")
        toast(names[layoutMode])
        saveView()
    }

    fun changeFont(d: Float) {
        var f = fontSp + d
        if (f < 7f) f = 7f
        if (f > 30f) f = 30f
        fontSp = f
        for (p in listOf(p1, p2)) p.applyFont()
        saveView()
    }

    // ---------------- file picking ----------------
    private fun askFiles() {
        if (p1.uriStr == null) {
            AlertDialog.Builder(this)
                .setTitle("Select Files")
                .setMessage("Select the first text file")
                .setPositiveButton("OK") { _, _ -> pickFile(1) }
                .show()
        } else if (p2.uriStr == null) {
            AlertDialog.Builder(this)
                .setTitle("Select Files")
                .setMessage("Select the second text file")
                .setPositiveButton("OK") { _, _ -> pickFile(2) }
                .show()
        }
    }

    fun pickFile(n: Int) {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, n)
    }

    @Deprecated("Deprecated in Java")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK || data == null) return
        val uri = data.data ?: return
        if (requestCode == 1 || requestCode == 2) {
            try {
                contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION)
            } catch (e: Exception) {
            }
            val p = panel(requestCode)
            p.page = 1
            p.currentMatch = -1
            p.searchTerm = ""
            p.lastSearchTerm = ""
            p.loadFile(uri.toString(), 0, 0, false)
            p.list.setSelection(0)
            updateFileLabels()
            saveView()
            if (requestCode == 1 && p2.uriStr == null) askFiles()
        } else if (requestCode == 3) {
            try {
                val os = contentResolver.openOutputStream(uri, "wt")
                if (os != null) {
                    try {
                        os.write((combined.joinToString("\n") + "\n").toByteArray(Charsets.UTF_8))
                    } finally {
                        os.close()
                    }
                }
                toast("Exported ${combined.size} mappings")
            } catch (e: Exception) {
                toast("Export failed: ${e.message}")
            }
        }
    }

    // ---------------- mapping actions ----------------
    fun saveMapping() {
        val p = panel(phase)
        if (p.selected.isEmpty()) return
        val dups = p.selected.filter { p.mappedSet.contains(it) }
        if (dups.isNotEmpty()) {
            toast("Already mapped: " + dups.take(10).joinToString(","))
            return
        }
        maps(phase).add(p.selected.toIntArray())
        p.mappedSet.addAll(p.selected)
        p.selected.clear()
        updateUi()
        saveMaps()
        saveView()
    }

    private fun clearSelection() {
        panel(phase).selected.clear()
        updateUi()
        saveView()
    }

    // In single-file layouts (2 = File 1 only, 3 = File 2 only) show the panel being switched to.
    private fun showOnlyIfSingle(n: Int) {
        if (layoutMode >= 2) {
            layoutMode = n + 1
            applyLayout()
        }
    }

    private fun switchTo(n: Int) {
        if (phase == n) {
            if (layoutMode >= 2 && layoutMode != n + 1) {
                showOnlyIfSingle(n)
                updateUi()
                saveView()
            } else {
                toast("Already mapping File $n")
            }
            return
        }
        confirm("Switch to File $n?\nFile $phase has ${maps(phase).size} mappings.") {
            phase = n
            panel(n).selected.clear()
            showOnlyIfSingle(n)
            updateUi()
            saveView()
        }
    }

    private fun doCombine() {
        combined.clear()
        val n = if (maps1.size > maps2.size) maps1.size else maps2.size
        for (i in 0 until n) {
            val f1 = if (i < maps1.size) maps1[i] else IntArray(0)
            val f2 = if (i < maps2.size) maps2[i] else IntArray(0)
            combined.add(f1.joinToString(",") + "=" + f2.joinToString(","))
        }
        saveMaps()
        toast("Created ${combined.size} combined mappings!")
    }

    private fun combine() {
        if (maps1.size != maps2.size) {
            confirm("Count mismatch — File 1: ${maps1.size}, File 2: ${maps2.size}\n\nContinue?") { doCombine() }
        } else {
            doCombine()
        }
    }

    private fun exportCombined() {
        if (combined.isEmpty()) {
            toast("Create combined mappings first.")
            return
        }
        val i = Intent(Intent.ACTION_CREATE_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "text/plain"
        i.putExtra(Intent.EXTRA_TITLE, "combined_mappings.txt")
        startActivityForResult(i, 3)
    }

    private fun setLinesPerPage() {
        val et = EditText(this)
        et.inputType = InputType.TYPE_CLASS_NUMBER
        et.setText(linesPerPage.toString())
        AlertDialog.Builder(this)
            .setTitle("Lines Per Page")
            .setMessage("Enter number of lines per page:\n(current: $linesPerPage)")
            .setView(et)
            .setPositiveButton("OK") { _, _ ->
                val v = et.text.toString().trim().toIntOrNull()
                if (v == null || v < 1 || v > 10000) {
                    toast("Enter a number from 1 to 10000")
                } else {
                    linesPerPage = v
                    for (p in listOf(p1, p2)) {
                        p.page = 1
                        p.refreshWindow()
                        if (!p.scrollMode) p.list.setSelection(0)
                    }
                    saveView()
                }
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    private fun afterMapChange() {
        rebuildMapped()
        saveMaps()
        updateUi()
    }

    // ---------------- view mappings dialog ----------------
    private fun showMappings() {
        val tab = IntArray(1)
        val btnT = arrayOfNulls<Button>(3)
        val lv = ListView(this)
        val emptyTv = label("No mappings yet.", 13f, Color.LTGRAY)
        val delRow = LinearLayout(this)
        delRow.orientation = LinearLayout.HORIZONTAL

        fun items(t: Int): List<String> {
            val out = ArrayList<String>()
            if (t == 0) {
                for (i in maps1.indices) out.add("${i + 1}. ${maps1[i].joinToString(",")}")
            } else if (t == 1) {
                for (i in maps2.indices) out.add("${i + 1}. ${maps2[i].joinToString(",")}")
            } else {
                for (i in combined.indices) out.add("${i + 1}. ${combined[i]}")
            }
            return out
        }

        fun refresh() {
            val t = tab[0]
            val list = items(t)
            lv.choiceMode = if (t < 2) ListView.CHOICE_MODE_MULTIPLE else ListView.CHOICE_MODE_NONE
            val layoutId = if (t < 2) android.R.layout.simple_list_item_multiple_choice else android.R.layout.simple_list_item_1
            lv.adapter = ArrayAdapter<String>(this, layoutId, list)
            lv.clearChoices()
            if (list.isNotEmpty()) {
                val last = list.size - 1
                lv.post { lv.setSelection(last) }
            }
            emptyTv.visibility = if (list.isEmpty()) View.VISIBLE else View.GONE
            delRow.visibility = if (t < 2) View.VISIBLE else View.GONE
            btnT[0]?.text = "File 1 (${maps1.size})"
            btnT[1]?.text = "File 2 (${maps2.size})"
            btnT[2]?.text = "Combined (${combined.size})"
            for (i in 0 until 3) btnT[i]?.alpha = if (i == t) 1f else 0.55f
        }

        fun deleteSelected() {
            val t = tab[0]
            if (t > 1) return
            val chk = lv.checkedItemPositions
            val idxs = ArrayList<Int>()
            for (i in 0 until chk.size()) {
                if (chk.valueAt(i)) idxs.add(chk.keyAt(i))
            }
            if (idxs.isEmpty()) {
                toast("Select mapping(s) to delete.")
                return
            }
            confirm("Delete ${idxs.size} mapping(s) from File ${t + 1}?") {
                idxs.sortDescending()
                val m = maps(t + 1)
                for (i in idxs) {
                    if (i < m.size) m.removeAt(i)
                }
                afterMapChange()
                refresh()
            }
        }

        fun deleteAll() {
            val t = tab[0]
            if (t > 1) return
            val m = maps(t + 1)
            if (m.isEmpty()) {
                toast("No mappings in File ${t + 1}.")
                return
            }
            confirm("Delete ALL ${m.size} mappings from File ${t + 1}?\nCannot be undone!") {
                m.clear()
                afterMapChange()
                refresh()
            }
        }

        val tabRow = LinearLayout(this)
        tabRow.orientation = LinearLayout.HORIZONTAL
        val colors = intArrayOf(col("#1976D2"), col("#E65100"), col("#673AB7"))
        for (i in 0 until 3) {
            val b = toolBtn("", colors[i]) {
                tab[0] = i
                refresh()
            }
            btnT[i] = b
            tabRow.addView(b)
        }
        delRow.addView(toolBtn("Delete\nSelected", col("#F44336")) { deleteSelected() })
        delRow.addView(toolBtn("Delete\nAll", col("#D32F2F")) { deleteAll() })

        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        box.addView(tabRow, LinearLayout.LayoutParams(MP, WC))
        box.addView(emptyTv, LinearLayout.LayoutParams(MP, WC))
        box.addView(lv, LinearLayout.LayoutParams(MP, dp(340)))
        box.addView(delRow, LinearLayout.LayoutParams(MP, WC))
        refresh()

        AlertDialog.Builder(this)
            .setTitle("Saved Mappings")
            .setView(box)
            .setPositiveButton("Close", null)
            .show()
    }

    // ---------------- duplicates ----------------
    private fun dupMap(m: List<IntArray>): Map<Int, List<Int>> {
        val d = HashMap<Int, ArrayList<Int>>()
        for (idx in m.indices) {
            for (ln in m[idx]) d.getOrPut(ln) { ArrayList() }.add(idx + 1)
        }
        return d.filter { it.value.size > 1 }
    }

    private fun combDup(side: Int): Map<Int, List<Int>> {
        val d = HashMap<Int, ArrayList<Int>>()
        for (idx in combined.indices) {
            val parts = combined[idx].split("=")
            if (parts.size == 2) {
                for (x in parts[side].split(",")) {
                    val v = x.trim().toIntOrNull()
                    if (v != null) d.getOrPut(v) { ArrayList() }.add(idx + 1)
                }
            }
        }
        return d.filter { it.value.size > 1 }
    }

    private fun showDuplicates() {
        val f1 = dupMap(maps1)
        val f2 = dupMap(maps2)
        val c1 = combDup(0)
        val c2 = combDup(1)
        if (f1.isEmpty() && f2.isEmpty() && c1.isEmpty() && c2.isEmpty()) {
            AlertDialog.Builder(this)
                .setTitle("No Duplicates")
                .setMessage("✓ No duplicates found!\nAll line numbers are unique.")
                .setPositiveButton("OK", null)
                .show()
            return
        }
        val sb = StringBuilder()
        val total = f1.size + f2.size + c1.size + c2.size
        sb.append("⚠ DUPLICATE LINE NUMBERS DETECTED ⚠\nFound $total total duplicate occurrences\n\n")
        fun sec(title: String, m: Map<Int, List<Int>>) {
            if (m.isEmpty()) return
            sb.append(title).append("\n\n")
            for (k in m.keys.sorted()) {
                val v = m[k]
                if (v != null) sb.append("Line $k in ${v.size} mappings: $v\n")
            }
            sb.append("\n")
        }
        sec("=== File 1 – Separate Mappings ===", f1)
        sec("=== File 1 – Combined Mappings ===", c1)
        sec("=== File 2 – Separate Mappings ===", f2)
        sec("=== File 2 – Combined Mappings ===", c2)
        val tv = TextView(this)
        tv.typeface = Typeface.MONOSPACE
        tv.textSize = 12f
        tv.setPadding(dp(12), dp(8), dp(12), dp(8))
        tv.text = sb.toString()
        val sv = ScrollView(this)
        sv.addView(tv)
        AlertDialog.Builder(this)
            .setTitle("Duplicate Report")
            .setView(sv)
            .setPositiveButton("Close", null)
            .show()
    }

    // ---------------- keyboard / mouse ----------------
    override fun dispatchKeyEvent(e: KeyEvent): Boolean {
        if (e.action == KeyEvent.ACTION_DOWN) {
            val f = currentFocus
            if (f is EditText) {
                if (e.keyCode == KeyEvent.KEYCODE_ESCAPE) {
                    hideKb(f)
                    return true
                }
            } else {
                val ctrl = (e.metaState and KeyEvent.META_CTRL_ON) != 0
                if (e.keyCode == KeyEvent.KEYCODE_S && !ctrl) {
                    saveMapping()
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_C && ctrl) {
                    lastPanel.copyCursor()
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_F && ctrl) {
                    lastPanel.findEt.requestFocus()
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_PAGE_DOWN) {
                    lastPanel.nextPage()
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_PAGE_UP) {
                    lastPanel.prevPage()
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_DPAD_LEFT) {
                    lastPanel.panByChars(if (ctrl) -50 else -10)
                    return true
                }
                if (e.keyCode == KeyEvent.KEYCODE_DPAD_RIGHT) {
                    lastPanel.panByChars(if (ctrl) 50 else 10)
                    return true
                }
            }
        }
        return super.dispatchKeyEvent(e)
    }

    private fun panelAt(x: Float, y: Float): Panel? {
        for (p in listOf(p1, p2)) {
            if (p.root.visibility != View.VISIBLE) continue
            val loc = IntArray(2)
            p.root.getLocationOnScreen(loc)
            if (x >= loc[0] && x <= loc[0] + p.root.width && y >= loc[1] && y <= loc[1] + p.root.height) return p
        }
        return null
    }

    override fun dispatchGenericMotionEvent(ev: MotionEvent): Boolean {
        if (ev.action == MotionEvent.ACTION_SCROLL) {
            val v = ev.getAxisValue(MotionEvent.AXIS_VSCROLL)
            val ctrl = (ev.metaState and KeyEvent.META_CTRL_ON) != 0
            val shift = (ev.metaState and KeyEvent.META_SHIFT_ON) != 0
            if (ctrl) {
                changeFont(if (v > 0f) 1f else -1f)
                return true
            }
            if (shift) {
                val p = panelAt(ev.rawX, ev.rawY)
                if (p != null) p.panByChars((-v * 8f).toInt())
                return true
            }
        }
        return super.dispatchGenericMotionEvent(ev)
    }
}
