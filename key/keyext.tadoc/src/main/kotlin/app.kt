package org.key_project.core.doc

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import de.uka.ilkd.key.nparser.KeYLexer
import de.uka.ilkd.key.nparser.KeYParser
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor
import de.uka.ilkd.key.nparser.ParsingFacade
import org.antlr.v4.runtime.CharStreams
import java.io.File

object App {
    @JvmStatic
    fun main(args: Array<String>) {
        GenDoc().main(args)
    }
}

class GenDoc() : CliktCommand() {
    val outputFolder by option("-o", "--output", help = "output folder", metavar = "FOLDER")
            .file().default(File("target"))

    val tacletFiles by argument("taclet-file", help = "")
            .file().multiple(required = true)

    val symbols = Index().also {
        val l = KeYLexer(CharStreams.fromString(""))
        (0..l.vocabulary.maxTokenType)
                .filter { l.vocabulary.getLiteralName(it) != null }
                .forEach { t ->
                    l.vocabulary.getSymbolicName(t)?.let { name ->
                        it += Any() to Symbol.Token(name, t)
                    }
                }
    }

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
            DocumentationFile(target, f, ctx, symbols).invoke()
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }

    fun generateIndex() {
        val f = File(outputFolder, "index.html")
        Indexfile(f, symbols).invoke()
    }
}

class Indexer(val self: String, val index: Index) : KeYParserBaseVisitor<Unit>() {
    override fun visitFile(ctx: KeYParser.FileContext) {
        index += ctx to IndexHelper.file(self)
        super.visitFile(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
        for (name in ctx.sortIds.simple_ident_dots()) {
            index += ctx to IndexHelper.sort(self, name.text)
        }
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
        index += ctx to IndexHelper.function(self, ctx.func_name.text)
    }

    override fun visitTransform_decl(ctx: KeYParser.Transform_declContext) {
        index += ctx to IndexHelper.transformer(self, ctx.trans_name.text)
    }

    override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
        index += ctx to IndexHelper.predicate(self, ctx.pred_name.text)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) {
        index += ctx to IndexHelper.taclet(self, ctx.name.text)
    }

    override fun visitChoice(ctx: KeYParser.ChoiceContext) {
        index += ctx to IndexHelper.choiceCategory(self, ctx.category.text)
        ctx.choice_option.forEach { co ->
            index += co to IndexHelper.choiceOption(self, ctx.category.text, co.text)
        }
    }
}

object IndexHelper {
    fun choiceCategory(page: String, cat: String): Symbol = Symbol.CATEGORY(cat, page)

    fun choiceOption(page: String, cat: String, option: String): Symbol =
            Symbol.OPTION(page, cat, option)

    fun taclet(page: String, text: String) =
            Symbol.TACLET(text, page, text)

    fun predicate(page: String, text: String) =
            Symbol.PREDICATE(text, page, text)

    fun function(page: String, text: String) =
            Symbol.FUNCTION(text, page, text)

    fun sort(page: String, text: String) =
            Symbol.SORT(text, page)

    fun transformer(page: String, text: String) =
            Symbol.TRANSFORMER(text, page, text)

    fun file(self: String) = Symbol.FILE(self)
}

/**
 * Represents a link to an entry.
 */
sealed class Symbol(
        val displayName: String,
        val url: String,
        val target: String) {
    val anchor = javaClass.simpleName + "-$target"
    val href = "$url#$anchor"

    class TACLET(displayName: String, page: String, id: String) : Symbol(displayName, page, id)
    class PREDICATE(displayName: String, page: String, id: String) : Symbol(displayName, page, id)
    class TRANSFORMER(displayName: String, page: String, id: String) : Symbol(displayName, page, id)
    class FUNCTION(displayName: String, page: String, id: String) : Symbol(displayName, page, id)
    class CATEGORY(displayName: String, page: String) : Symbol(displayName, page, displayName)
    class OPTION(page: String, val cat: String, val option: String) : Symbol("$cat:$option", page, "${cat}_$option")
    class SORT(displayName: String, page: String) : Symbol(displayName, page, displayName)
    class FILE(self: String) : Symbol(self, self.replace(".html", ""), "root")


    class Token(val display: String, val tokenType: Int) : Symbol(display,
            "https://key-project.org/docs/grammar/", display)

    class External(url: String) : Symbol("", url, "")
}

typealias Index = ArrayList<Pair<Any, Symbol>>
