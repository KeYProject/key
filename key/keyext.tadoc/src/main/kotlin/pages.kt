package org.key_project.core.doc

import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import org.antlr.v4.runtime.ParserRuleContext
import org.commonmark.ext.autolink.AutolinkExtension
import org.commonmark.ext.gfm.strikethrough.StrikethroughExtension
import org.commonmark.ext.gfm.tables.TablesExtension
import org.commonmark.ext.ins.InsExtension
import org.commonmark.parser.Parser
import org.commonmark.renderer.html.HtmlRenderer
import org.key_project.core.doc.Markdown.markdown
import java.io.File

abstract class DefaultPage(
        val target: File,
        val pageTitle: String,
        val index: Index) {
    var brandTitle: String = "KeY Logic Documentation"
    var tagLine: String = "Auto-generated from the KeY files."
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

                    nav("nav") {
                        ul("nav-list") {
                            li("nav-item") {
                                a(classes = "pure-button", href = "index.html") { +"Startpage" }
                                a(classes = "pure-button", href = "https://key-project.org/docs/") { +"KeY Docs" }
                            }
                        }
                    }

                    h3 { +"Overview" }
                    nav("nav") {
                        ul("nav-list") {
                            val cat = index.asSequence()
                                    .map { (_, b) -> b }
                                    .filter { it.url == self }
                                    .filter { it !is Symbol.FILE && it !is Symbol.External }
                                    .groupBy { it.javaClass }
                            cat.forEach { c ->
                                li() {
                                    +c.key.simpleName
                                    ul {
                                        c.value.sortedBy { it.displayName }.forEach {
                                            li { a(it.href) { +it.displayName } }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

    open fun commonFooter(div: DIV) {
        div.div("footer") {
            div("pure-menu pure-menu-horizontal") {
                ul {
                    li("pure-menu-item") { a(href = "http://purecss.io/", classes = "pure-menu-link") { +"About" } }
                    li("pure-menu-item") { a(href = "http://twitter.com/yuilibrary/", classes = "pure-menu-link") { +"Twitter" } }
                    li("pure-menu-item") { a(href = "http://github.com/pure-css/pure/", classes = "pure-menu-link") { +"GitHub" } }
                }
            }
        }
    }
}

class Indexfile(target: File, index: Index) : DefaultPage(target, "Index Page", index) {
    override fun content(div: DIV) {
        div.div {
            h1 { +"Index page" }
            val symbols = index.map { (a, b) -> b }
            region("Choice categories", symbols.filterIsInstance<Symbol.CATEGORY>())
            region("Choice options", symbols.filterIsInstance<Symbol.OPTION>())
            region("Sorts", symbols.filterIsInstance<Symbol.SORT>())
            region("Predicates", symbols.filterIsInstance<Symbol.PREDICATE>())
            region("Functions", symbols.filterIsInstance<Symbol.FUNCTION>())
            region("Transformers", symbols.filterIsInstance<Symbol.TRANSFORMER>())
            region("Taclets", symbols.filterIsInstance<Symbol.TACLET>())
            region("Files", symbols.filterIsInstance<Symbol.FILE>())
        }
    }
}

class DocumentationFile(target: File, val keyFile: File, val ctx: KeYParser.FileContext, index: Index)
    : DefaultPage(target, "${keyFile.nameWithoutExtension} -- Documentation", index) {
    override fun content(div: DIV) {
        div.h1 { +keyFile.name }

        ctx.DOC_COMMENT().forEach {
            div.markdown(it.text)
        }

        //small { +file.relativeTo(File(".").absoluteFile).toString() }
        ctx.accept(FileVisitor(self, div, index))
    }
}


class FileVisitor(val self: String,
                  val tagConsumer: DIV,
                  val index: Index) : KeYParserBaseVisitor<Unit>() {
    override fun visitFile(ctx: KeYParser.FileContext) {
        val symbol = index.lookup(ctx)
        tagConsumer.div { id = symbol!!.target }
        super.visitFile(ctx)
    }

    override fun visitDecls(ctx: KeYParser.DeclsContext?) {
        super.visitDecls(ctx)
    }

    override fun visitProblem(ctx: KeYParser.ProblemContext?) {
        super.visitProblem(ctx)
    }

    override fun visitOne_include_statement(ctx: KeYParser.One_include_statementContext) {
        tagConsumer.div { +"Requires: ${ctx.text}" }
        super.visitOne_include_statement(ctx)
    }

    override fun visitOne_include(ctx: KeYParser.One_includeContext?) {
        super.visitOne_include(ctx)
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
            catsym?.target?.let { id = it }
            h3 {
                +ctx.category.text
            }

            markdown(ctx.DOC_COMMENT?.text)

            printDefinition(ctx, index)

            ctx.choice_option.forEachIndexed { i, co ->
                val optsym = index.lookup(co)
                div("doc option") {
                    h4 { +co.text }
                    //TODO+ctx.DOC_COMMENT(i + 1).text
                }
            }
        }

    }

    override fun visitSort_decls(ctx: KeYParser.Sort_declsContext?) {
        tagConsumer.h2 { +"Sorts" }
        super.visitSort_decls(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
        for (s in ctx.sortIds.simple_ident_dots()) {
            val symbol = index.lookup(s)
            tagConsumer.div("doc sort") {
                symbol?.target?.let { id = it }
                h3("sort") {
                    +s.text
                }
                printDefinition(ctx, index)
            }
        }
    }

    override fun visitProg_var_decls(ctx: KeYParser.Prog_var_declsContext?) {
        super.visitProg_var_decls(ctx)
    }

    override fun visitPred_decls(ctx: KeYParser.Pred_declsContext?) {
        tagConsumer.h2 { +"Predicates" }
        super.visitPred_decls(ctx)
    }


    override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
        val symbol = index.lookup(ctx)
        tagConsumer.div("doc pred") {
            symbol?.target?.let { id = it }
            h3("sort") {
                +ctx.pred_name.text
            }
            printDefinition(ctx, index)
        }
    }

    override fun visitFunc_decls(ctx: KeYParser.Func_declsContext?) {
        tagConsumer.h2 { +"Functions" }
        super.visitFunc_decls(ctx)
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
        val symbol = index.lookup(ctx)
        tagConsumer.div("doc func") {
            symbol?.anchor?.let { id = it }
            h3 { +ctx.func_name.text }
            markdown(ctx.DOC_COMMENT()?.text)
            printDefinition(ctx, index)
        }
    }

    override fun visitRulesOrAxioms(ctx: KeYParser.RulesOrAxiomsContext) {
        tagConsumer.h2 { +"Taclets" }

        tagConsumer.div {
            if (ctx.choices?.option().isNullOrEmpty()) {
                +"No choice condition specified"
            } else {
                +"Enabled under choices:"
                ctx.choices?.option()?.forEach {
                    val target = index.findChoice(it.cat.text, it.value.text)?.href ?: ""
                    a(target) { +it.text }
                    +" "
                }
            }
        }

        super.visitRulesOrAxioms(ctx)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) {
        val symbol = index.lookup(ctx)
        tagConsumer.div("doc taclet") {
            symbol?.target?.let { id = it }
            h3("taclet") {
                +ctx.name.text
            }
            printDefinition(ctx, index)
        }
    }
}

private fun Index.findChoice(text: String?, text1: String?): Symbol? {
    val t = "$text:$text1"
    return asSequence().map { (a, b) -> b }.find {
        it is Symbol.OPTION && it.displayName == t
    }
}

fun DIV.region(title: String, types: Iterable<Symbol>) {
    div("region") {
        h2 { +title }
        div("links") {
            types.sortedBy { it.displayName }.forEach {
                a(it.href, classes = it.javaClass.simpleName) { +it.displayName }
                +" "
            }
        }
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

    fun DIV.markdown(doc: String?) {
        if (doc == null) return
        div("markdown") {
            unsafe { +renderer.render(parser.parse(doc.trim('/', '!', '*'))) }
        }
    }
}

private fun DIV.printDefinition(ctx: ParserRuleContext, index: Index) {
    div("raw") {
        code {
            unsafe { +ctx.accept(PrettyPrinter(index)) }
        }
        small {
            val source = ctx.getStart().tokenSource
            +"defined in: ${File(source.sourceName).name} Line: ${ctx.start.line} Offset :${ctx.start.charPositionInLine}"
        }
    }
}

private fun Index.lookup(s: Any): Symbol? = this.find { (a, _) -> a == s }?.second

