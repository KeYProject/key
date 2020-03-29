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

val GIT_VERSION by lazy {
    val pb = ProcessBuilder("git", "describe", "--all")
            .redirectErrorStream(true)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
    val p = pb.start();
    p.waitFor()
    String(p.inputStream.readAllBytes())
}

/**
 * Ideas:
 */
class GenDoc() : CliktCommand() {
    val outputFolder by option("-o", "--output", help = "output folder", metavar = "FOLDER")
            .file().default(File("target"))

    val inputFiles by argument("taclet-file", help = "")
            .file().multiple(required = true)

    val tacletFiles by lazy {
        inputFiles.flatMap {
            when {
                it.isDirectory ->
                    it.walkTopDown().filter { it.name.endsWith(".key") }.toList()
                else -> listOf(it)
            }
        }
    }

    val symbols = Index().also {
        val l = KeYLexer(CharStreams.fromString(""))
        (0..l.vocabulary.maxTokenType)
                .filter { l.vocabulary.getLiteralName(it) != null }
                .forEach { t ->
                    l.vocabulary.getSymbolicName(t)?.let { name ->
                        it += Symbol.token(name, t)
                        //println("## ${name} {: #Token-${name}}\n")
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
            println("Analyze: $f")
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
        index += Symbol.file(self, ctx)
        super.visitFile(ctx)
    }

    override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
        for (name in ctx.sortIds.simple_ident_dots()) {
            index += Symbol.sort(self, name.text, name)
        }
    }

    override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
        index += Symbol.function(self, ctx.func_name.text, ctx)
    }

    override fun visitTransform_decl(ctx: KeYParser.Transform_declContext) {
        index += Symbol.transformer(self, ctx.trans_name.text, ctx)
    }

    override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
        index += Symbol.predicate(self, ctx.pred_name.text, ctx)
    }

    override fun visitTaclet(ctx: KeYParser.TacletContext) {
        index += Symbol.taclet(self, ctx.name.text, ctx)
    }

    override fun visitChoice(ctx: KeYParser.ChoiceContext) {
        index += Symbol.choiceCategory(self, ctx.category.text)
        ctx.choice_option.forEach { co ->
            index += Symbol.choiceOption(self, ctx.category.text, co.text, co)
        }
    }

    override fun visitRuleset_decls(ctx: KeYParser.Ruleset_declsContext) {
        ctx.id.forEach {
            index += Symbol.ruleset(it.text, self, it)
        }
    }

    override fun visitOne_contract(ctx: KeYParser.One_contractContext) {
        index += Symbol.contract(ctx.contractName.text, self, ctx)
    }

    override fun visitOne_invariant(ctx: KeYParser.One_invariantContext) {
        index += Symbol.invariant(ctx.invName.text, self, ctx)
    }
}

/**
 * Represents a link to an entry.
 */
open class Symbol(
        val displayName: String,
        val url: String,
        val target: String = displayName,
        val type: Type,
        val ctx: Any? = null) {
    open val anchor = javaClass.simpleName + "-$target"
    open val href = "$url#$anchor"

    enum class Type(val navigationTitle: String) {
        CATEGORY("Choice categories"),
        OPTION("Choice options"),
        SORT("Sorts"),
        PREDICATE("Predicates"),
        FUNCTION("Functions"),
        TRANSFORMER("Transformers"),
        RULESET("Rulesets"),
        TACLET("Taclets"),
        CONTRACT("Contracts"),
        INVARIANT("Invariants"),
        FILE("Files"),
        TOKEN("t"), EXTERNAL("ext");
    }


    companion object {
        fun choiceCategory(page: String, cat: String, ctx: Any? = null): Symbol = Symbol(cat, page, cat, Type.CATEGORY, ctx)
        fun choiceOption(page: String, cat: String, option: String, ctx: Any? = null): Symbol = Symbol("$cat:$option", page, "$cat-$option", Type.OPTION, ctx)
        fun taclet(page: String, text: String, ctx: Any? = null) = Symbol(text, page, text, Type.TACLET, ctx)
        fun predicate(page: String, text: String, ctx: Any? = null) = Symbol(text, page, text, Type.PREDICATE, ctx)
        fun function(page: String, text: String, ctx: Any? = null) = Symbol(text, page, text, Type.FUNCTION, ctx)
        fun sort(page: String, text: String, ctx: Any? = null) = Symbol(text, page, type = Type.SORT, ctx = ctx)
        fun transformer(page: String, text: String, ctx: Any? = null) = Symbol(text, page, text, Type.TRANSFORMER, ctx)
        fun file(self: String, ctx: Any? = null) = Symbol(self.replace(".html", ""), self, "root", Type.FILE, ctx)
        fun ruleset(name: String, page: String, ctx: Any? = null) = Symbol(name, page, name, Type.RULESET, ctx)
        fun token(display: String, tokenType: Int) = TokenSymbol(display, tokenType)
        fun external(url: String, anchor: String = "", ctx: Any? = null) = object : Symbol("", url, "", Type.EXTERNAL, ctx) {
            override val anchor: String = anchor
            override val href = url
        }

        fun contract(name: String, self: String, ctx: Any? = null) = Symbol(name, self, name, Type.CONTRACT, ctx)
        fun invariant(name: String, self: String, ctx: Any? = null) = Symbol(name, self, name, Type.INVARIANT, ctx)
    }

    override fun toString(): String {
        return "Symbol(displayName='$displayName', url='$url', target='$target', type=$type, ctx=$ctx, anchor='$anchor', href='$href')"
    }
}

data class TokenSymbol(val display: String, val tokenType: Int)
    : Symbol(display, "https://key-project.org/docs/grammar/", display, Type.TOKEN)

typealias Index = ArrayList<Symbol>

