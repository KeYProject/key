/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.soundiness;

import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.settings.TacletOptionsSettings;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.StrategySettings;

import org.key_project.prover.rules.RuleApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Static utility class for analyzing proof soundiness.
 * Generates an HTML report directly.
 * 
 * @author opencode
 * @since 2.13
 */
public final class SoundinessAnalyzer {
    
    private static final Logger LOGGER = LoggerFactory.getLogger(SoundinessAnalyzer.class);
    
    private static final String GENERAL_DISCLAIMER = """
        This report reflects the soundiness status of your verification with respect to KeY's modeling assumptions. \
        KeY provides full support for Java 1.4 and many subsequent language features, though not all Java constructs are modeled. \
        The following limitations apply: reflection is not supported; native methods are not verified but can be specified with contracts—if these contracts are faithful, verification proceeds soundly; \
        verification assumes sequential execution without multi-threading; and floating-point arithmetic is faithfully modeled according to IEEE 754 semantics. \
        Temporary inconsistencies may exist in the prover (e.g., String switch labels currently use identity comparison instead of equals; see issue #1234). \
        These limitations are independent of the taclet option choices analyzed below. \
        Note that this analysis is modulo bugs in KeY itself.
        """;
    
    private SoundinessAnalyzer() {
        // Utility class - no instances
    }
    
    /**
     * Generates an HTML soundiness report for the given proof.
     * 
     * @param proof the proof to analyze
     * @return HTML string containing the complete report
     */
    public static String generateHTMLReport(Proof proof) {
        if (proof == null) {
            throw new IllegalArgumentException("Proof cannot be null");
        }
        
        List<TacletOptionEntry> tacletOptions = analyzeTacletOptions(proof);
        SourceStats sourceStats = analyzeSource(proof);
        ProofStats proofStats = analyzeProofTree(proof);
        
        StringBuilder html = new StringBuilder();
        html.append("<html><head><style>")
            .append("body { font-family: sans-serif; margin: 10px; font-size: 14pt; }")
            .append("h2 { border-bottom: 1px solid #888; padding-bottom: 5px; margin-top: 20px; }")
            .append("h3 { margin-top: 15px; }")
            .append(".warning { background-color: #fff3cd; border-left: 4px solid #ffc107; padding: 8px; margin: 5px 0; }")
            .append(".critical { background-color: #f8d7da; border-left: 4px solid #dc3545; padding: 8px; margin: 5px 0; }")
            .append(".info { background-color: #d1ecf1; border-left: 4px solid #17a2b8; padding: 8px; margin: 5px 0; }")
            .append(".unsound { color: #dc3545; font-weight: bold; }")
            .append(".incomplete { color: #fd7e14; font-weight: bold; }")
            .append("xxxul { margin: 5px 0; }")
            .append("xxxli { margin: 3px 0; }")
            .append("</style></head><body>");
        
        String timestamp = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm")
            .format(ZonedDateTime.now(ZoneId.systemDefault()));
        
        html.append("<h1>KeY Soundiness Report</h1>")
            .append("<p><b>Proof:</b> ").append(escapeHtml(proof.name().toString()))
            .append(" | <b>Generated:</b> ").append(timestamp).append("</p>");
        
        // Compartment 1: General KeY Settings
        html.append("<h2>1. General KeY Soundiness</h2>");
        html.append("<p>").append(GENERAL_DISCLAIMER).append("</p>");

        // Compartment 2: Taclet Options
        html.append("<h2>2. Taclet Option Soundiness</h2>");
        if (tacletOptions.isEmpty()) {
            html.append("<p><i>All taclet options are at default/safe settings.</i></p>");
        } else {
            html.append("<ul>");
            for (TacletOptionEntry entry : tacletOptions) {
                String choiceText = entry.choice();
                int colonIdx = choiceText.indexOf(':');
                String displayChoice = colonIdx >= 0 ? choiceText.substring(colonIdx + 1) : choiceText;
                
                html.append("<li class='").append(entry.cssClass()).append("'>")
                    .append(escapeHtml(displayChoice));
                if (entry.impact() != null) {
                    html.append(": ").append(escapeHtml(entry.impact()));
                }
                if (entry.features() != null && entry.features().length > 0) {
                    html.append("<br><small><i>Affects: ");
                    for (int i = 0; i < entry.features().length; i++) {
                        if (i > 0) html.append(", ");
                        html.append(escapeHtml(entry.features()[i]));
                    }
                    html.append("</i></small>");
                }
                html.append("</li>");
            }
            html.append("</ul>");
        }
        
        // Compartment 3: Source Analysis
        html.append("<h2>3. Source Analysis</h2>");
        if (sourceStats.javaFileCount() == 0 && sourceStats.keyFileCount() == 0) {
            html.append("<p><i>Detailed source analysis not yet implemented.</i></p>");
        } else {
            html.append("<ul>")
                .append("<li>Java files loaded: ").append(sourceStats.javaFileCount()).append("</li>")
                .append("<li>Specification (.key) files: ").append(sourceStats.keyFileCount()).append("</li>");
            
            if (!sourceStats.loadedFiles().isEmpty()) {
                html.append("<li>Loaded files: ");
                for (int i = 0; i < Math.min(10, sourceStats.loadedFiles().size()); i++) {
                    if (i > 0) html.append(", ");
                    html.append(escapeHtml(sourceStats.loadedFiles().get(i)));
                }
                if (sourceStats.loadedFiles().size() > 10) {
                    html.append(", ...");
                }
                html.append("</li>");
            }
            
            if (sourceStats.totalMethods() > 0) {
                int percentage = (sourceStats.methodsWithContracts() * 100) / sourceStats.totalMethods();
                html.append("<li>JML contract coverage: ").append(sourceStats.methodsWithContracts())
                    .append("/").append(sourceStats.totalMethods()).append(" methods (")
                    .append(percentage).append("%)</li>");
            }
            
            if (!sourceStats.parseWarnings().isEmpty()) {
                html.append("<li>Parse warnings: ").append(sourceStats.parseWarnings().size()).append("</li>");
            }
            
            if (!sourceStats.unsupportedFeatures().isEmpty()) {
                html.append("<li>Unsupported features: ").append(sourceStats.unsupportedFeatures().size()).append("</li>");
            }
            
            html.append("</ul>");
        }
        
        // Compartment 4: Proof Tree Analysis
        html.append("<h2>4. Proof Tree Analysis</h2>");
        html.append("<h3>Goal Statistics</h3><ul>")
            .append("<li>Total goals: ").append(proofStats.totalGoals()).append("</li>")
            .append("<li>Closed goals: ").append(proofStats.closedGoals()).append("</li>")
            .append("<li>Open goals: ").append(proofStats.openGoals()).append("</li>");
        if (proofStats.cachedGoals() > 0) {
            html.append("<li>Cached goals: ").append(proofStats.cachedGoals())
                .append(" (from proof cache)</li>");
        }
        html.append("</ul>");
        
        if (!proofStats.lemmasUsed().isEmpty()) {
            html.append("<h3>User-Defined Lemmas Used</h3><ul>");
            for (LemmaUsage lemma : proofStats.lemmasUsed()) {
                String status = lemma.proved() ? "proved" : "<span class='incomplete'>not proved</span>";
                html.append("<li>").append(escapeHtml(lemma.name()))
                    .append(" (used ").append(lemma.count()).append(" times, ")
                    .append(status).append(")</li>");
            }
            html.append("</ul>");
        }
        
        if (!proofStats.assumptionsUsed().isEmpty()) {
            html.append("<h3 class='unsound'>Assumptions Introduced</h3><ul>");
            for (AssumptionUsage assumption : proofStats.assumptionsUsed()) {
                html.append("<li>").append(escapeHtml(assumption.location())).append(": ")
                    .append(escapeHtml(assumption.formula()));
                if (assumption.reason() != null && !assumption.reason().isEmpty()) {
                    html.append(" (").append(escapeHtml(assumption.reason())).append(")");
                }
                html.append("</li>");
            }
            html.append("</ul>");
        }
        
        html.append("<h3>Rule Applications</h3><ul>")
            .append("<li>Total steps: ").append(proofStats.totalSteps()).append("</li>")
            .append("<li>Automated: ").append(proofStats.automatedSteps()).append("</li>")
            .append("<li>Interactive: ").append(proofStats.interactiveSteps()).append("</li>");
        
        if (!proofStats.mostUsedRules().isEmpty()) {
            html.append("<li>Most used rules:<ul>");
            for (String rule : proofStats.mostUsedRules()) {
                html.append("<li>").append(escapeHtml(rule)).append("</li>");
            }
            html.append("</ul></li>");
        }
        html.append("</ul>");
        
        html.append("</body></html>");
        return html.toString();
    }
    
    private static String escapeHtml(String text) {
        if (text == null) {
            return "";
        }
        return text.replace("&", "&amp;")
                   .replace("<", "&lt;")
                   .replace(">", "&gt;")
                   .replace("\"", "&quot;");
    }
    
    private static List<GeneralKeYWarning> analyzeGeneralKeY(Proof proof) {
        List<GeneralKeYWarning> warnings = new ArrayList<>();
        
        long maxMemory = Runtime.getRuntime().maxMemory();
        if (maxMemory < 1024 * 1024 * 1024) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.CRITICAL,
                "Memory",
                "Very limited memory available (" + (maxMemory / 1024 / 1024) + " MB)",
                "Increase heap size with -Xmx flag (e.g., -Xmx4g)"
            ));
        } else if (maxMemory < 2L * 1024 * 1024 * 1024) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.WARNING,
                "Memory",
                "Limited memory available (" + (maxMemory / 1024 / 1024) + " MB)",
                "Consider increasing heap size with -Xmx flag for large proofs"
            ));
        }
        
        ChoiceSettings choiceSettings = proof.getSettings().getChoiceSettings();
        Map<String, String> choices = choiceSettings.getDefaultChoices();
        
        if ("initialisation:disableStaticInitialisation".equals(choices.get("initialisation"))) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.CRITICAL,
                "Static Initialization",
                "Static constructors are not analyzed",
                "Enable static initialization for complete verification (may increase complexity)"
            ));
        }
        
        GeneralSettings generalSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        if (!generalSettings.isUseJML()) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.CRITICAL,
                "JML Specifications",
                "JML specifications are ignored",
                "Enable JML in settings to verify behavioral properties"
            ));
        }
        
        if (!generalSettings.isEnsureSourceConsistency()) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.INFO,
                "Source Code",
                "Source file changes may not be detected during verification",
                "Enable source consistency checking if source files change during verification"
            ));
        }
        
        StrategySettings strategySettings = proof.getSettings().getStrategySettings();
        int maxSteps = strategySettings.getMaxSteps();
        if (maxSteps > 0 && maxSteps < 100000) {
            warnings.add(new GeneralKeYWarning(
                GeneralKeYWarning.Level.WARNING,
                "Proof Search",
                "Automated proof search limited to " + maxSteps + " steps",
                "Increase step limit for more complex proofs"
            ));
        }
        
        return warnings;
    }
    
    private static List<TacletOptionEntry> analyzeTacletOptions(Proof proof) {
        List<TacletOptionEntry> entries = new ArrayList<>();
        
        ChoiceSettings choiceSettings = proof.getSettings().getChoiceSettings();
        Map<String, String> choices = choiceSettings.getDefaultChoices();
        
        for (Map.Entry<String, String> entry : choices.entrySet()) {
            String choice = entry.getValue();
            
            TacletOptionsSettings.ChoiceEntry baseEntry = 
                TacletOptionsSettings.createChoiceEntry(choice);
            
            String impact = getPlainEnglishImpact(choice);
            String[] features = getAffectedFeatures(choice);
            
            if (impact != null && !impact.isEmpty()) {
                entries.add(new TacletOptionEntry(choice, impact, features, baseEntry.isUnsound(), baseEntry.isIncomplete()));
            }
        }
        
        return entries;
    }
    
    private static String getPlainEnglishImpact(String choice) {
        return switch (choice) {
            case "runtimeExceptions:ignore" -> "Assumes no null pointer, divide-by-zero, or array bounds errors occur";
            case "intRules:arithmeticSemanticsIgnoringOF" -> "Integer overflow is ignored; arithmetic wraps around like in Java";
            case "initialisation:disableStaticInitialisation" -> "Static field initializers and static blocks are skipped";
            case "Strings:off" -> "String operations are not analyzed";
            case "programRules:None" -> "Java language constructs are not processed";
            case "runtimeExceptions:ban" -> "Any implicit runtime exception is treated as program failure (overly strict but safe)";
            case "intRules:arithmeticSemanticsCheckingOF" -> "Integer arithmetic is mathematical; overflow must be explicitly prevented";
            case "integerSimplificationRules:minimal" -> "Limited simplification rules for integer arithmetic";
            case "JavaCard:on" -> "JavaCard mode enabled - sound for JavaCard, unsound for regular Java";
            case "JavaCard:off" -> "JavaCard features disabled - sound for regular Java";
            case "assertions:on" -> "Java assertions are enabled - sound only if JVM runs with -ea flag";
            case "assertions:off" -> "Java assertions are disabled - sound only if JVM runs without -ea flag";
            default -> null;
        };
    }
    
    private static String[] getAffectedFeatures(String choice) {
        return switch (choice) {
            case "runtimeExceptions:ignore" -> new String[] {"NullPointerException", "ArithmeticException", "ArrayIndexOutOfBoundsException"};
            case "intRules:arithmeticSemanticsIgnoringOF" -> new String[] {"int arithmetic", "long arithmetic", "overflow detection"};
            case "initialisation:disableStaticInitialisation" -> new String[] {"static fields", "static initialization blocks"};
            case "Strings:off" -> new String[] {"String concatenation", "String.length()", "String.charAt()"};
            case "programRules:None" -> new String[] {"all Java statements", "method calls", "assignments"};
            case "JavaCard:on" -> new String[] {"transaction mechanism", "atomicity", "persistence"};
            default -> new String[0];
        };
    }
    
    private static SourceStats analyzeSource(Proof proof) {
        return new SourceStats(0, 0, new ArrayList<>(), new ArrayList<>(), 0, 0, new ArrayList<>());
    }
    
    private static ProofStats analyzeProofTree(Proof proof) {
        int totalGoals = 0;
        int closedGoals = 0;
        int openGoals = 0;
        int cachedGoals = 0;
        
        List<LemmaUsage> lemmasUsed = new ArrayList<>();
        List<AssumptionUsage> assumptionsUsed = new ArrayList<>();
        int interactiveSteps = 0;
        int automatedSteps = 0;
        
        Map<String, Integer> ruleUsageCount = new HashMap<>();
        
        Set<Node> openGoalNodes = new HashSet<>();
        for (de.uka.ilkd.key.proof.Goal goal : proof.openGoals()) {
            openGoalNodes.add(goal.node());
        }
        
        Iterator<Node> nodeIterator = proof.root().subtreeIterator();
        while (nodeIterator.hasNext()) {
            Node node = nodeIterator.next();
            
            boolean isOpenGoal = openGoalNodes.contains(node);
            if (isOpenGoal) {
                openGoals++;
                totalGoals++;
            } else {
                closedGoals++;
                totalGoals++;
                
                if (node.lookup(ClosedBy.class) != null) {
                    cachedGoals++;
                }
            }
            
            RuleApp app = node.getAppliedRuleApp();
            if (app != null) {
                String ruleName = app.rule().name().toString();
                ruleUsageCount.put(ruleName, ruleUsageCount.getOrDefault(ruleName, 0) + 1);
                
                if (app instanceof TacletApp tacletApp) {
                    Taclet taclet = tacletApp.rule();
                    
                    if (taclet.name().toString().contains("lemma") || 
                        taclet.name().toString().contains("Lemma")) {
                        String lemmaName = taclet.name().toString();
                        boolean alreadyTracked = lemmasUsed.stream().anyMatch(l -> l.name().equals(lemmaName));
                        if (!alreadyTracked) {
                            lemmasUsed.add(new LemmaUsage(lemmaName, false, 1));
                        }
                    }
                    
                    if (ruleName.contains("assume") || ruleName.contains("Assume")) {
                        assumptionsUsed.add(new AssumptionUsage(
                            node.sequent().toString(),
                            "Goal " + node.serialNr(),
                            "User assumption"));
                    }
                }
                
                if (isOpenGoal) {
                    for (de.uka.ilkd.key.proof.Goal goal : proof.openGoals()) {
                        if (goal.node() == node && goal.isAutomatic()) {
                            automatedSteps++;
                            break;
                        }
                    }
                } else {
                    interactiveSteps++;
                }
            }
        }
        
        List<String> mostUsedRules = ruleUsageCount.entrySet().stream()
            .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
            .limit(5)
            .map(entry -> entry.getKey() + " (" + entry.getValue() + ")")
            .collect(Collectors.toList());
        
        return new ProofStats(
            totalGoals, closedGoals, openGoals, cachedGoals,
            lemmasUsed, assumptionsUsed,
            automatedSteps + interactiveSteps, automatedSteps, interactiveSteps,
            mostUsedRules
        );
    }
    
    record GeneralKeYWarning(Level level, String category, String userMessage, String recommendation) {
        enum Level {
            INFO("info"), WARNING("warning"), CRITICAL("critical");
            private final String cssClass;
            Level(String cssClass) { this.cssClass = cssClass; }
            String cssClass() { return cssClass; }
        }
    }
    
    record TacletOptionEntry(String choice, String impact, String[] features, boolean unsound, boolean incomplete) {
        String cssClass() { return unsound ? "unsound" : incomplete ? "incomplete" : ""; }
    }
    
    record SourceStats(int javaFileCount, int keyFileCount, List<String> loadedFiles,
                       List<String> parseWarnings, int totalMethods, int methodsWithContracts,
                       List<String> unsupportedFeatures) {}
    
    record ProofStats(int totalGoals, int closedGoals, int openGoals, int cachedGoals,
                      List<LemmaUsage> lemmasUsed, List<AssumptionUsage> assumptionsUsed,
                      int totalSteps, int automatedSteps, int interactiveSteps,
                      List<String> mostUsedRules) {}
    
    record LemmaUsage(String name, boolean proved, int count) {}
    
    record AssumptionUsage(String formula, String location, String reason) {}
}
