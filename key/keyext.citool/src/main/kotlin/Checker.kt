package de.uka.ilkd.key

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import de.uka.ilkd.key.api.KeYApi
import de.uka.ilkd.key.control.AbstractUserInterfaceControl
import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine
import de.uka.ilkd.key.parser.Location
import de.uka.ilkd.key.settings.ChoiceSettings
import de.uka.ilkd.key.settings.ProofSettings
import de.uka.ilkd.key.speclang.Contract
import java.io.File
import kotlin.system.exitProcess


/**
 * A small interface for a checker scripts
 * @author Alexander Weigl
 * @version 1 (21.11.19)
 */
class Checker : CliktCommand() {
    val includes by option("").multiple()
    val verbose by option().flag("--no-verbose")
    val dryRun by option("--dry-run").flag()

    val classpath by option("--classpath", "-cp").multiple()

    val bootClassPath by option("--bootClassPath", "-bcp")

    val onlyContracts by option("--contract",
            help = "")
            .multiple()

    val forbidContracts by option("--forbid-contact",
            help = "")
            .multiple()

    val inputFile by argument("INPUT",
            help = "")
            .multiple(true)

    val proofPath by option("--proof-path").multiple()

    val tacletChoices by option("-T").multiple()

    private var choiceSettings: ChoiceSettings? = null

    private fun initEnvironment() {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            val env: KeYEnvironment<*> = KeYEnvironment.load(File("."), null, null, null)
            env.dispose()
        }
        choiceSettings = ProofSettings.DEFAULT_SETTINGS.choiceSettings
    }

    var errorlevel = 0

    override fun run() {
        inputFile.forEach { run(it) }
        exitProcess(errorlevel)
    }

    fun run(input: String) {
        println("* $input: ")

        val pm = KeYApi.loadProof(File(input),
                classpath.map { File(it) },
                bootClassPath?.let { File(it) },
                includes.map { File(it) })

        val contracts = pm.proofContracts
                .filter { it.name in onlyContracts || onlyContracts.isEmpty() }

        for (c in contracts) {
            print("  * ${c.name}")

            if (c.name in forbidContracts) {
                println(" ... excluded (--forbid-contract)")
            } else {
                if (dryRun) {
                    println(" ... skipped (--dry-run).")
                } else {
                    val proofApi = pm.startProof(c)

                    val proofFile = findProofFile(c)
                    val scriptFile = findScriptFile(c)

                    var autoMode = true
                    if (proofFile != null) {
                        println()
                        print("    * Proof found: $proofFile. Try loading.")
                        autoMode = false
                    }
                    if (scriptFile != null) {
                        println()
                        print("    * Script found: $scriptFile. Try proofing.")
                        autoMode = false

                        val script = File(scriptFile).readText()
                        val engine = ProofScriptEngine(script,
                                Location(scriptFile, 1, 1))
                        val startTime = System.currentTimeMillis()
                        engine.execute(
                                proofApi.env.ui as AbstractUserInterfaceControl, proofApi.proof)
                        val endTime = System.currentTimeMillis()
                        print("... script took ${endTime - startTime}...")
                    }

                    if (autoMode) {
                        val startTime = System.currentTimeMillis()
                        proofApi.env.proofControl.startAutoMode(proofApi.proof)
                        val endTime = System.currentTimeMillis()
                        print("... auto-mode took ${endTime - startTime}...")
                    }

                    if (proofApi.proof.closed()) println("proof closed!") else println("proof remains open")
                }
            }
        }
    }

    val proofFileCandidates by lazy {
        val candidates = ArrayList<String>()
        proofPath.forEach { candidates.addAll(File(it).list()) }
        candidates
    }

    private fun findProofFile(c: Contract): String? = proofFileCandidates.find { it.startsWith(c.displayName) && (it.endsWith(".proof") || it.endsWith(".proof.gz")) }

    private fun findScriptFile(c: Contract): String? = proofFileCandidates.find { it.startsWith(c.displayName) && (it.endsWith(".txt") || it.endsWith(".pscript")) }

}

fun main(args: Array<String>) = Checker().main(args)
