package org.key_project.core.doc

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import de.uka.ilkd.key.nparser.ParsingFacade
import kotlinx.html.stream.appendHTML
import java.io.File

object App {
    @JvmStatic
    fun main(args: Array<String>) {
        GenDoc().main(args)
    }
}

typealias Symbols = ArrayList<Pair<Any, Symbol>>

class GenDoc() : CliktCommand() {
    val outputFolder by option("-o", "--output", help = "output folder", metavar = "FOLDER")
            .file().default(File("target"))

    val tacletFiles by argument("taclet-file", help = "")
            .file().multiple(required = true)

    val symbols = Symbols()

    override fun run() {
        outputFolder.mkdirs()
        copyStaticFiles()
        tacletFiles.map(::index).zip(tacletFiles).forEach { (ctx, f) -> run(ctx, f) }
        generateIndex()
    }

    fun copyStaticFiles() {
        copyStaticFile("style.css")
    }

    fun copyStaticFile(s: String) {
        javaClass.getResourceAsStream("/static/$s")?.use { input ->
            File(outputFolder, s).outputStream().use { out ->
                input.copyTo(out)
            }
        }
    }

    fun index(f: File): KeYParser.FileContext {
        val ast = ParsingFacade.parseFile(f)
        val ctx = ParsingFacade.getParseRuleContext(ast)
        val self = f.nameWithoutExtension + ".html"
        ctx.accept(Indexer(self, symbols))
        return ctx
    }

    fun run(ctx: KeYParser.FileContext, f: File) {
        try {
            val target = File(outputFolder, f.nameWithoutExtension + ".html")
            target.bufferedWriter().use {
                it.appendHTML(true).writeDocumentationFile(target.name, f, ctx, symbols)
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }

    fun generateIndex(): Unit {
        val f = File(outputFolder, "index.html")
        f.bufferedWriter().use {
            it.appendHTML(true).writeIndexFile(f.name, symbols)
        }
    }
}

class Indexer(val self: String, val symbols: MutableList<Pair<Any, Symbol>>) : KeYParserBaseVisitor<Unit>() {
    override fun visitFile(ctx: KeYParser.FileContext) {
        symbols += ctx to IndexHelper.file(self)
        super.visitFile(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
        for (name in ctx.sortIds.simple_ident_dots()) {
            symbols += ctx to IndexHelper.sort(self, name.text)
        }
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
        symbols += ctx to IndexHelper.function(self, ctx.func_name.text)
    }

    override fun visitTransform_decl(ctx: KeYParser.Transform_declContext) {
        symbols += ctx to IndexHelper.transformer(self, ctx.trans_name.text)
    }

    override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
        symbols += ctx to IndexHelper.predicate(self, ctx.pred_name.text)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) {
        symbols += ctx to IndexHelper.taclet(self, ctx.name.text)
    }

    override fun visitChoice(ctx: KeYParser.ChoiceContext) {
        symbols += ctx to IndexHelper.choiceCategory(self, ctx.category.text)
        ctx.choice_option.forEach { co ->
            symbols += co to IndexHelper.choiceOption(self, ctx.category.text, co.text)
        }
    }
}

object IndexHelper {
    fun choiceCategory(page: String, cat: String): Symbol =
            Symbol(cat, page, "$page-$cat", Symbol.Type.CATEGORY)

    fun choiceOption(page: String, cat: String, option: String): Symbol =
            Symbol("$cat:$option", page, "${cat}_$option", Symbol.Type.OPTION)

    fun taclet(page: String, text: String) =
            Symbol(text, page, text, Symbol.Type.TACLET)

    fun predicate(page: String, text: String) =
            Symbol(text, page, text, Symbol.Type.PREDICATE)

    fun function(page: String, text: String) =
            Symbol(text, page, text, Symbol.Type.FUNCTION)

    fun sort(page: String, text: String) =
            Symbol(text, page, text, Symbol.Type.SORT)

    fun transformer(page: String, text: String) =
            Symbol(text, page, text, Symbol.Type.TRANSFORMER)

    fun file(self: String) = Symbol(self, self, "root", Symbol.Type.FILE)
}

data class Symbol(val displayName: String,
                  val page: String,
                  val id: String,
                  val type: Type) {
    enum class Type {
        TACLET, SORT, PREDICATE, TRANSFORMER, FUNCTION, CATEGORY, OPTION, FILE
    }

    val url = "$page#$type.$id"
}
