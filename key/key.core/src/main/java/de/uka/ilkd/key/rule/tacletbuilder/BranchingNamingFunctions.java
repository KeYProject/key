package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public final class BranchingNamingFunctions {
    private static Map<String, Function<String[], BranchNamingFunction>> functionList = new HashMap<>();

    private BranchingNamingFunctions() {
    }

    static {
        registerFunction("\\nameLabelOf", NameLabelOf::new);
    }


    public static void registerFunction(String name, Function<String[], BranchNamingFunction> fn) {
        functionList.put(name, fn);
    }


    private static final Pattern PATTERN_FUNC = Pattern.compile("(?<n>\\\\\\w+?)(\\(((\\w+?)(,(\\w+?))*)?\\))?");

    public static String[] parse(String name) {
        List<String> a = new ArrayList<>();
        var stream = new CommonTokenStream(ParsingFacade.createLexer(CharStreams.fromString(name)));
        if (stream.LA(1) != KeYLexer.ESC_IDENT) return null;
        a.add(stream.LT(1).getText());
        stream.consume();
        if (stream.LA(1) == KeYLexer.LPAREN) {
            stream.consume();
            if (stream.LA(1) != KeYLexer.RPAREN) {
                if (stream.LA(1) != KeYLexer.IDENT)
                    throw new IllegalStateException("expected name after '(' but got: " + stream.LA(1));
                a.add(stream.LT(1).getText());
                stream.consume();
                do {
                    if (stream.LA(1) == KeYLexer.COMMA) {
                        stream.consume();
                        if (stream.LA(1) != KeYLexer.IDENT)
                            throw new IllegalArgumentException("Expected name after comma");
                        a.add(stream.LT(1).getText());
                        stream.consume();
                    }
                } while (stream.LA(1) != KeYLexer.RPAREN);
            }
        }
        return a.toArray(new String[0]);
    }

    @Nullable
    public static BranchNamingFunction find(String name) {
        var args = parse(name);
        if (args == null) return null;
        var fnName = args[0];
        var factory = functionList.get(fnName);
        if (factory == null) {
            return null;
        }
        return factory.apply(args);
    }

    public static class NameLabelOf implements BranchNamingFunction {
        private final String matchedSchemaVariableName;

        public NameLabelOf(String matchedSchemaVariableName) {
            this.matchedSchemaVariableName = matchedSchemaVariableName;
        }

        public NameLabelOf(String... args) {
            this(args[1]);
        }


        @Override
        public String getName(Services services, SequentChangeInfo currentSequent, TacletApp tacletApp,
                              MatchConditions matchConditions) {
            var sv = matchConditions.getInstantiations().lookupVar(
                    new Name(matchedSchemaVariableName));
            var value = matchConditions.getInstantiations().getInstantiation(sv);
            try {
                var term = (Term) value;
                var name = term.getLabel(SpecNameLabel.NAME);
                if (name == null) return null;
                return (String) name.getChild(0);
            } catch (ClassCastException e) {
                e.printStackTrace();
                return "blubb";
            }
        }
    }
}
