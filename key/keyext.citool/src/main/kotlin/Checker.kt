package de.uka.ilkd.key

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import de.uka.ilkd.key.api.KeYApi
import de.uka.ilkd.key.control.AbstractUserInterfaceControl
import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine
import de.uka.ilkd.key.parser.Location
import de.uka.ilkd.key.settings.ChoiceSettings
import de.uka.ilkd.key.settings.ProofSettings
import de.uka.ilkd.key.speclang.Contract
import de.uka.ilkd.key.util.MiscTools
import java.io.File
import kotlin.system.exitProcess


/**
 * A small interface for a checker scripts
 * @author Alexander Weigl
 * @version 1 (21.11.19)
 */
class Checker : CliktCommand() {
    val includes by option(
            help = "defines additional key files to be included"
    ).multiple()
    val autoModeStep by option("--auto-mode-max-step", metavar = "INT",
            help = "maximal amount of steps in auto-mode [default:10000]")
            .int().default(10000)
    val verbose by option(help = "verbose output, currently unused").flag("--no-verbose")
    val dryRun by option("--dry-run", help = "skipping the proof reloading, scripts execution and auto mode." +
            " Useful for finding the contract names").flag()

    val classpath by option("--classpath", "-cp",
            help = "additional classpaths").multiple()

    val bootClassPath by option("--bootClassPath", "-bcp",
            help = "set the bootclasspath")

    val onlyContracts by option("--contract",
            help = "whitelist contracts by their names")
            .multiple()

    val forbidContracts by option("--forbid-contact",
            help = "forbid contracts by their name")
            .multiple()

    val inputFile by argument("JAVA-KEY-FILE",
            help = "key, java or a folder")
            .multiple(true)

    val proofPath by option("--proof-path",
            help = "folders to look for proofs and script files")
            .multiple()

    //val tacletChoices by option("-T").multiple()

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
            val filename = MiscTools.toValidFileName(c.name);

            if (c.name in forbidContracts) {
                println(" ... excluded (--forbid-contract) ")
            } else {
                if (dryRun) {
                    println(" ... skipped (--dry-run). ")
                } else {
                    val proofApi = pm.startProof(c)
                    val proof = proofApi.proof
                    require(proof != null)
                    proof?.settings?.strategySettings?.maxSteps = autoModeStep
                    ProofSettings.DEFAULT_SETTINGS.strategySettings.maxSteps = autoModeStep

                    val proofFile = findProofFile(filename)
                    val scriptFile = findScriptFile(filename)

                    var autoMode = true
                    if (proofFile != null) {
                        println()
                        print("    * Proof found: $proofFile. Try loading. ")
                        autoMode = false
                    }
                    if (scriptFile != null) {
                        println()
                        print("    * Script found: $scriptFile. Try proofing. ")
                        autoMode = false

                        val script = File(scriptFile).readText()
                        val engine = ProofScriptEngine(script,
                                Location(scriptFile, 1, 1))
                        val startTime = System.currentTimeMillis()
                        engine.execute(
                                proofApi.env.ui as AbstractUserInterfaceControl, proofApi.proof)
                        val endTime = System.currentTimeMillis()
                        print(" ... script took ${endTime - startTime} ms... ")
                    }

                    if (autoMode) {
                        val startTime = System.currentTimeMillis()
                        proofApi.env.proofControl.startAndWaitForAutoMode(proof)
                        val endTime = System.currentTimeMillis()
                        print("... auto-mode took ${endTime - startTime} ms... ")
                    }

                    if (proof.closed()) {
                        println("PROOF CLOSED! Rule apps: ${proof.statistics.totalRuleApps}")
                    } else {
                        println("${proof.openGoals().size()} remains open")
                        errorlevel = 1
                    }
                    proof.dispose()
                }
            }
        }
    }

    val proofFileCandidates by lazy {
        val candidates = ArrayList<String>()
        proofPath.forEach { candidates.addAll(File(it).list()) }
        candidates
    }

    private fun findProofFile(filename: String): String? = proofFileCandidates.find { it.startsWith(filename) && (it.endsWith(".proof") || it.endsWith(".proof.gz")) }

    private fun findScriptFile(filename: String): String? = proofFileCandidates.find { it.startsWith(filename) && (it.endsWith(".txt") || it.endsWith(".pscript")) }

}

fun main(args: Array<String>) = Checker().main(args)
