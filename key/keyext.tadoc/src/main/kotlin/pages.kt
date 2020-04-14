package org.key_project.core.doc

import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import org.commonmark.ext.autolink.AutolinkExtension
import org.commonmark.ext.gfm.strikethrough.StrikethroughExtension
import org.commonmark.ext.gfm.tables.TablesExtension
import org.commonmark.ext.ins.InsExtension
import org.commonmark.parser.Parser
import org.commonmark.renderer.html.HtmlRenderer
import org.key_project.core.doc.Markdown.markdown
import org.key_project.core.doc.org.key_project.core.doc.GitBlameService
import java.io.File
import java.util.*

abstract class DefaultPage(
        val target: File,
        val pageTitle: String,
        val index: Index) {
    var brandTitle: String = "KeY Logic Documentation"
    var tagLine: String = "Defined symbols in the KeY System"
    val self = target.name

    operator fun invoke() {
        target.bufferedWriter().use {
            it.appendHTML(true).html {
                head {
                    title(pageTitle)
                    styleLink("style.css")
                }
                body {
                    div("pure-g") {
                        id = "layout"
                        commonHeader(this)
                        div("content pure-u-3-4") {
                            content(this)
                            commonFooter(this)
                        }
                    }
                }
            }
        }
    }

    abstract fun content(div: DIV)

    open fun commonHeader(body: DIV) =
            body.div("sidebar pure-u-1-4") {
                div("0header") {
                    h1("brand-title") { +brandTitle }
                    h2("brand-tagline") { +tagLine }

                    span { +"Generated from version: $GIT_VERSION on ${Date()}" }

                    nav("nav") {
                        ul("nav-list") {
                            li("nav-item") {
                                a(classes = "pure-button", href = "index.html") { +"Startpage" }
                                a(classes = "pure-button", href = "usage.html") { +"Usage Index" }
                                a(classes = "pure-button", href = "https://key-project.org/docs/") { +"KeY Docs" }
                            }
                        }
                    }

                    h3 { +"Overview" }
                    nav("nav") {
                        ul("nav-list") {
                            navigation()
                        }
                    }
                }
            }

    open fun UL.navigation() {
        val cat = index.asSequence()
                .filter { it.url == self }
                .filter { it.type != Symbol.Type.FILE && it.type != Symbol.Type.EXTERNAL }
                .groupBy { it.type }
        cat.forEach { c ->
            li() {
                +c.key.navigationTitle
                ul {
                    c.value.sortedBy { it.displayName }.forEach {
                        li { a(it.href) { +it.displayName } }
                    }
                }
            }
        }
    }

    open fun commonFooter(div: DIV) {
        div.div("footer") {
            div("pure-menu pure-menu-horizontal") {
                ul {
                    li("pure-menu-item") { a(href = "https://key-project.org/docs/grammar/#how-to-doc", classes = "pure-menu-link") { +"About" } }
                }
            }
        }
    }
}

class Indexfile(target: File, index: Index) : DefaultPage(target, "Index Page", index) {
    override fun content(div: DIV) {
        div.div {
            h1 { +"Index page" }
            Symbol.Type.values().forEach {
                region(it)
            }
        }
    }

    override fun UL.navigation() {
    }

    fun DIV.region(title: Symbol.Type) {
        val types = index.filter { it.type == title }
        div("region") {
            h2 { id = title.name; +title.navigationTitle }
            if (types.isNotEmpty()) {
                div("links") {
                    types.sortedBy { it.displayName }.forEach {
                        a(it.href, classes = it.javaClass.simpleName) { +it.displayName }
                        +" "
                    }
                }
            } else {
                div("no-entries") { +"No entry in this category" }
            }
        }
    }
}


class UsageIndexFile(target: File, index: Index, val usageIndex: UsageIndex) : DefaultPage(target, "Usage", index) {
    val usedItems =
            usageIndex.entries.groupBy { (a, _) -> a.type }
                    .toList()
                    .sortedBy { (a, _) -> a }

    override fun content(div: DIV) {
        div.div {
            h1 { +"Usage Index" }
            for ((category, usedSymbols) in usedItems) {
                region(category, usedSymbols)
            }
        }
    }

    private fun DIV.region(category: Symbol.Type,
                           usedSymbols: List<MutableMap.MutableEntry<Symbol, MutableList<Symbol>>>) {
        h2("") {
            id = category.name
            +category.navigationTitle
        }
        section {
            usedSymbols
                    .sortedBy { (a, _) -> a.displayName }
                    .forEach { (used, where) ->
                        h3 { a(href = used.href) { id = used.anchor; +(used.displayName) } }
                        where.sortedBy { it.displayName }
                                .distinctBy { it.href }
                                .forEach {
                                    ul {
                                        li {
                                            a(href = it.href, classes = "symbol ${it.type}") {
                                                +(it.displayName + " (${it.type}) ")
                                            }
                                        }
                                    }
                                }
                    }
        }
    }

    override fun UL.navigation() {
        usedItems.forEach { (type, seq) ->
            li {
                a("#${type.name}") { +type.navigationTitle }
                ul {
                    seq.sortedBy { (a, _) -> a.displayName }
                            .forEach { (used, _) ->
                                li { a(href = "#${used.anchor}", classes = used.type.name) { +(used.displayName) } }
                            }
                }
            }
        }
    }
}

class DocumentationFile(target: File, val keyFile: File, val ctx: KeYParser.FileContext, index: Index,
                        val usageIndex: UsageIndex)
    : DefaultPage(target, "${keyFile.nameWithoutExtension} -- Documentation", index) {


    override fun content(div: DIV) {
        div.h1 { +keyFile.name }

        ctx.DOC_COMMENT().forEach {
            div.markdown(it.symbol)
        }

        //small { +file.relativeTo(File(".").absoluteFile).toString() }
        ctx.accept(FileVisitor(self, div, index, usageIndex))
    }
}


class FileVisitor(val self: String,
                  val tagConsumer: DIV,
                  val index: Index,
                  val usageIndex: UsageIndex) : KeYParserBaseVisitor<Unit>() {

    private lateinit var symbol: Symbol
    private val printer: PrettyPrinter
        get() = PrettyPrinter(index, symbol, true, usageIndex)

    override fun visitFile(ctx: KeYParser.FileContext) {
        symbol = index.lookup(ctx)!!
        tagConsumer.div { id = symbol.anchor }
        super.visitFile(ctx)
    }

    override fun visitProblem(ctx: KeYParser.ProblemContext?) {
        super.visitProblem(ctx)
    }

    override fun visitOne_include_statement(ctx: KeYParser.One_include_statementContext) {
        tagConsumer.div { +"Requires: ${ctx.text}" }
        super.visitOne_include_statement(ctx)
    }

    override fun visitOne_include(ctx: KeYParser.One_includeContext) {
        tagConsumer.div("include") { +"requires ${ctx.text}" }
    }

    override fun visitOptions_choice(ctx: KeYParser.Options_choiceContext?) {
        super.visitOptions_choice(ctx)
    }

    override fun visitActivated_choice(ctx: KeYParser.Activated_choiceContext?) {
        super.visitActivated_choice(ctx)
    }

    override fun visitOption_decls(ctx: KeYParser.Option_declsContext?) {
        super.visitOption_decls(ctx)
    }

    override fun visitChoice(ctx: KeYParser.ChoiceContext) {
        val catsym = index.lookup(ctx)
        tagConsumer.div("doc category") {
            h3 {
                id = catsym?.anchor ?: ""
                +ctx.category.text
            }

            ctx.maindoc.forEach { markdown(it)}

            printDefinition(ctx)

            ctx.optionDecl().forEachIndexed { i, co ->
                val optsym = index.lookup(co)
                div("doc option") {
                    h4 {
                        id = optsym?.anchor ?: ""
                        +co.IDENT.text
                    }
                    markdown(co.DOC_COMMENT)
                }
            }
        }
    }

    override fun visitSort_decls(ctx: KeYParser.Sort_declsContext?) {
        tagConsumer.h2 { id = "sorts"; +"Sorts" }
        super.visitSort_decls(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
        for (s in ctx.sortIds.simple_ident_dots()) {
            symbol = index.lookup(s)!!
            tagConsumer.div("doc sort") {
                h3("sort") {
                    id = symbol.anchor
                    +s.text
                }
                printDefinition(ctx)
            }
        }
    }

    override fun visitTransform_decl(ctx: KeYParser.Transform_declContext) {
        symbol = index.lookup(ctx)!!
        tagConsumer.div("doc transformer") {
            h3("transformer") {
                id = symbol.anchor
                +ctx.trans_name.text
            }
            printDefinition(ctx)
        }
    }

    override fun visitTransform_decls(ctx: KeYParser.Transform_declsContext?) {
        tagConsumer.h2 { +"Transfomers" }
        super.visitTransform_decls(ctx)
    }

    override fun visitPred_decls(ctx: KeYParser.Pred_declsContext?) {
        tagConsumer.h2 { +"Predicates" }
        super.visitPred_decls(ctx)
    }


    override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
        symbol = index.lookup(ctx)!!
        tagConsumer.div("doc predicate") {
            h3("sort") {
                id = symbol.anchor
                +ctx.pred_name.text
            }
            printDefinition(ctx)
        }
    }

    override fun visitFunc_decls(ctx: KeYParser.Func_declsContext?) {
        tagConsumer.h2 { +"Functions" }
        super.visitFunc_decls(ctx)
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
        val symbol = index.lookup(ctx)
        tagConsumer.div("doc function") {
            h3 {
                id = symbol?.anchor ?: ""
                +ctx.func_name.text
            }
            markdown(ctx.DOC_COMMENT()?.symbol)
            printDefinition(ctx)
        }
    }

    override fun visitRulesOrAxioms(ctx: KeYParser.RulesOrAxiomsContext) {
        tagConsumer.h2 { +"Taclets" }

        tagConsumer.div {
            if (ctx.choices?.option().isNullOrEmpty()) {
                +"No choice condition specified"
            } else {
                +"Enabled under choices: "
                ctx.choices?.option()?.forEach {
                    val target = index.findChoice(it.cat.text, it.value.text)?.href ?: ""
                    a(target, classes = "symbol choice") { +it.text }
                    +" "
                }
            }
        }

        super.visitRulesOrAxioms(ctx)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) {
        symbol = index.lookup(ctx)!!
        tagConsumer.div("doc taclet") {
            h3("taclet") {
                id = symbol.anchor
                +ctx.name.text
            }
            printDefinition(ctx)
        }
    }

    private fun DIV.printDefinition(ctx: ParserRuleContext) {
        div("raw") {
            code {
                unsafe { +ctx.accept(printer) }
            }
            small {
                val source = ctx.getStart().tokenSource
                +"defined in: ${File(source.sourceName).name} Line: ${ctx.start.line} Offset :${ctx.start.charPositionInLine}"
            }
            /*div {
                val file = ctx.start.tokenSource.sourceName
                val lineStart = ctx.start.line
                val lineStop = ctx.stop.line
                val infos = GitBlameService.getLastAuthorsWithDates(file, lineStart, lineStop)
                val last5Changes =
                        infos.sortedByDescending { it.timestamp }.distinctBy { it.author }.take(5)
                last5Changes.forEach {
                    span {
                        a(href = "https://git.key-project.org/key/key/-/commit/${it.gitCommit}") {
                            +(it.author + " on " + it.timestamp)
                        }
                    }
                }
            }*/
            /*div("git last-update") {
                val file = ctx.start.tokenSource.sourceName
                val lineStart = ctx.start.line
                val lineStop = ctx.stop.line
                val it = GitBlameService.lastUpdated(file, lineStart, lineStop)
                span {
                    a(href = "https://git.key-project.org/key/key/-/commit/${it.gitCommit}") {
                        +(it.author + " on " + it.timestamp)
                    }
                }
            }*/
        }
    }
}

private fun Index.findChoice(text: String?, text1: String?): Symbol? {
    val t = "$text:$text1"
    return asSequence().find {
        it.type == Symbol.Type.OPTION && it.displayName == t
    }
}


object Markdown {
    private val extensions = arrayListOf(TablesExtension.create(),
            AutolinkExtension.create(),
            InsExtension.create(),
            StrikethroughExtension.create())

    private val parser = Parser.builder()
            .extensions(extensions)
            .build()
    private val renderer = HtmlRenderer.builder()
            .extensions(extensions)
            .build()

    fun DIV.markdown(doc: Token?) {
        if (doc == null) return
        div("markdown") {
            val regex = "^\\s{0,${doc.charPositionInLine}}".toRegex()
            val text = doc.text
                    .trim('/', '!', '*')
                    .replace(regex, "")
                    .replaceAll(replacements)
            unsafe { +renderer.render(parser.parse(text)) }
        }
    }

    val replacements = listOf(
            "@choiceDefaultOption" to "This is the default option.",
            "@choiceUnsound" to """**This option is unsound**""",
            "@choiceIncomplete" to """**This option is incomplete**"""
    )
}

private fun String.replaceAll(replacements: List<Pair<String, String>>): String =
        replacements.fold(this, {acc, pair -> acc.replace(pair.first, pair.second)})

private fun Index.lookup(s: Any): Symbol? = this.find { it.ctx == s }

