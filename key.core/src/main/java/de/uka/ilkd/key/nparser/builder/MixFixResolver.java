package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import edu.kit.kastel.formal.mixfix.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jspecify.annotations.NonNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class MixFixResolver {

    private final MixFixRuleCollection<Term, Token> ruleCollection = new MixFixRuleCollection<>();

    private final Services services;

    public MixFixResolver(Services services) {
        this.services = services;

        // adding primary rules
        ruleCollection.addRule(new IntegerRule());
        ruleCollection.addRule(new ParenthesesRule());
        ruleCollection.addRule(new IdentifierRule());
        // ... others as well
    }

    public Term resolve(KeYParser.TermContext ctx) throws MixFixException {
        List<Token> tokens = extractTokens(ctx);
        // Currently there is ~ at the beginning and end of mixfix parts
        tokens.remove(0);
        tokens.remove(tokens.size()-1);
        MixFixParser<Term, Token> parser = new MixFixParser<>(ruleCollection);
        return parser.parseExpression(tokens);
    }

    public static List<Token> extractTokens(ParserRuleContext ctx) {
        List<Token> result = new ArrayList<>(1024);
        extractTokens(result, ctx);
        return result;
    }
    private static void extractTokens(List<Token> tokens, ParserRuleContext ctx) {
        for (ParseTree child : ctx.children) {
            if (child instanceof TerminalNode tn) {
                tokens.add(tn.getSymbol());
            } else {
                extractTokens(tokens, (ParserRuleContext) child);
            }
        }
    }

    public void addMixFixRule(Function functionSymbol, List<Token> mixfix) {
        Matcher<Token>[] matchers = new Matcher[mixfix.size()];
        int left = extractPrecedence(mixfix.get(0));
        int right = extractPrecedence(mixfix.get(mixfix.size() - 1));
        for (int i = 0; i < matchers.length; i++) {
            Token token = mixfix.get(i);
            if(token != null && token.getType() != KeYLexer.MIXFIX_HOLE && !token.getText().equals("_")) {
                matchers[i] = t -> t.getText().equals(token.getText()) && t.getType() == token.getType();
            }
        }
        ruleCollection.addRule(new KeYRule(functionSymbol, matchers, left, right));
    }

    private int extractPrecedence(Token token) {
        if(token.getType() == KeYLexer.MIXFIX_HOLE) {
            String num = token.getText().substring(2);
            return Integer.parseInt(num);
        } else {
            return 0;
        }
    }

    class KeYRule extends SequenceRule<Term, Token> {

        private final Function functionSymbol;
        protected KeYRule(Function functionSymbol, Matcher<Token>[] sequence, int leftBinding, int rightBinding) {
            super(sequence, leftBinding, rightBinding);
            this.functionSymbol = functionSymbol;
        }

        @Override
        protected Term makeResult(@NonNull ADTList<Term> results) {
            return services.getTermFactory().createTerm(functionSymbol, results.toList());
        }
    }

    private class IntegerRule implements MixFixRule<Term, Token> {

        @Override
        public boolean isLeftRecursive() {
            return false;
        }

        @Override
        public ADTList<ParseContext<Term, Token>> parse(ParseContext<Term, Token> context, int minBinding) {
            Token t = context.getCurrentToken();
            DebugLog.enter(context, minBinding);

            if (t.getType() == KeYLexer.INT_LITERAL) {
                context = context.consumeToken();
                context = context.setResult(services.getTermBuilder().zTerm(t.getText()));
                DebugLog.leave(context);
                return ADTList.singleton(context);
            } else {
                DebugLog.leave("nil");
                return ADTList.nil();
            }
        }
    }

    private static class ParenthesesRule extends SequenceRule<Term, Token> {

        protected ParenthesesRule() {
            super(Arrays.<Matcher<Token>>asList(
                    t -> t.getType() == KeYLexer.LPAREN,
                    null,
                    t -> t.getType() == KeYLexer.RPAREN).toArray(Matcher[]::new), 0, 0);
        }

        @Override
        protected Term makeResult(@NonNull ADTList<Term> results) {
            assert results.size() == 1;
            return results.hd();
        }
    }

    private class IdentifierRule implements MixFixRule<Term, Token> {
        @Override
        public boolean isLeftRecursive() {
            return false;
        }

        @Override
        public ADTList<ParseContext<Term, Token>> parse(ParseContext<Term, Token> context, int minBinding) {
            Token t = context.getCurrentToken();
            DebugLog.enter(context, minBinding);

            if (t.getType() == KeYLexer.IDENT) {
                String img = t.getText();
                Operator f = services.getNamespaces().functions().lookup(img);
                if (f == null) {
                    f = services.getNamespaces().programVariables().lookup(img);
                }
                if (f != null) {
                    context = context.consumeToken();
                    context = context.setResult(services.getTermFactory().createTerm(f));
                    DebugLog.leave(context);
                    return ADTList.singleton(context);
                }
            }
            DebugLog.leave("nil");
            return ADTList.nil();
        }
    }

}
