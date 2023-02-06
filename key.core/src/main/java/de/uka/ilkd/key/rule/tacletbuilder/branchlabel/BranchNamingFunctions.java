package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

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
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Token;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public final class BranchNamingFunctions {
    private static final Map<String, Function<List<String>, BranchNamingFunction>> functionList = new HashMap<>();
    private static final Logger LOGGER = LoggerFactory.getLogger(BranchNamingFunctions.class);

    private BranchNamingFunctions() {
    }

    static {
        registerFunction("\\nameLabelOf", NameLabelOf::new);

        //for testing and debugging purpose
        registerFunction("\\test", args ->
                (services, currentSequent, tacletApp, matchConditions) ->
                        "[" + String.join("|", args) + "]");
    }


    public static void registerFunction(String name, Function<List<String>, BranchNamingFunction> fn) {
        LOGGER.info("Register branch name function: {}", name);
        functionList.put(name, fn);
    }

    @Nonnull
    public static BranchNamingFunction find(String text) {
        if (!text.contains("\\")) {
            return new SimpleStringLabel(text);
        }
        var p = new MiniLabelParser(text);
        p.parse();
        return (services, currentSequent, tacletApp, matchConditions) ->
                p.branchNamingFunctions.stream().map(it ->
                                it.getName(services, currentSequent, tacletApp, matchConditions))
                        .collect(Collectors.joining(""));
    }

    public static class NameLabelOf implements BranchNamingFunction {
        private final String matchedSchemaVariableName;

        public NameLabelOf(String matchedSchemaVariableName) {
            this.matchedSchemaVariableName = matchedSchemaVariableName;
        }

        public NameLabelOf(List<String> args) {
            this(args.get(1));
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

    private static class SimpleStringLabel implements BranchNamingFunction {
        private final String label;

        private SimpleStringLabel(String label) {
            this.label = label;
        }

        @Override
        public String getName(Services services, SequentChangeInfo currentSequent,
                              TacletApp tacletApp, MatchConditions matchConditions) {
            return label;
        }
    }

    private static class MiniLabelParser {
        final List<BranchNamingFunction> branchNamingFunctions = new ArrayList<>();
        final KeYLexer stream;
        int current = -1;
        final List<? extends Token> tokens;
        Token token;

        public MiniLabelParser(String text) {
            stream = ParsingFacade.createLexer(CharStreams.fromString(text));
            tokens = stream.getAllTokens();
            consume();
        }

        public void parse() {
            do {
                if (token.getType() == KeYLexer.ESC_IDENT) {
                    parseBranchLabel();
                } else {
                    branchNamingFunctions.add(new SimpleStringLabel(token.getText()));
                    consume();
                }
            } while (token.getType() != IntStream.EOF);
        }

        private void parseBranchLabel() {
            var args = new ArrayList<String>();
            args.add(token.getText());
            consumeWS();
            if (token.getType() == KeYLexer.LPAREN) {
                consumeWS();
                if (token.getType() != KeYLexer.RPAREN) {
                    if (token.getType() != KeYLexer.IDENT)
                        throw new IllegalStateException("expected text after '(' but got: " + token);
                    args.add(token.getText());
                    consumeWS();
                    do {
                        if (token.getType() == KeYLexer.COMMA) {
                            consumeWS();
                            if (token.getType() != KeYLexer.IDENT)
                                throw new IllegalArgumentException("Expected text after comma");
                            args.add(token.getText());
                            consumeWS();
                        } else if (token.getType() == KeYLexer.RPAREN) {
                            break;
                        } else {
                            throw new IllegalArgumentException("Unexpected token: " + token);
                        }
                    } while (token.getType() != KeYLexer.RPAREN);
                }
                consume();
            }
            var factory = functionList.get(args.get(0));
            if (factory == null) {
                throw new IllegalStateException(
                        "A BranchNamingFunction with name " + args.get(0) + " is unknown.");
            }
            branchNamingFunctions.add(factory.apply(args));
        }

        private void consumeWS() {
            do {
                consume();
            } while (token.getType() == KeYLexer.WS);
        }

        private void consume() {
            current++;
            if (current >= tokens.size()) {
                token = new CommonToken(Token.EOF);
            } else {
                token = tokens.get(current);
            }
        }
    }
}
