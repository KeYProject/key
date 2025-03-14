/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeYParser.ProofScriptExpressionContext;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.meta.ConversionException;
import de.uka.ilkd.key.scripts.meta.Converter;
import de.uka.ilkd.key.scripts.meta.NoSpecifiedConverterException;
import de.uka.ilkd.key.scripts.meta.ValueInjector;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.CharStreams;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
@NullMarked
public class EngineState {
    public static final Logger LOGGER = LoggerFactory.getLogger(EngineState.class);

    private final Proof proof;
    private final ProofScriptEngine engine;

    private final AbbrevMap abbrevMap = new AbbrevMap();
    private final ValueInjector valueInjector = createDefaultValueInjector();
    private final ExprEvaluator exprEvaluator = new ExprEvaluator(this);

    private @Nullable Consumer<ProofScriptEngine.Message> observer;
    private Path baseFileName = Paths.get(".");

    private @Nullable Goal goal;
    private @Nullable Node lastSetGoalNode;

    /**
     * If set to true, outputs all commands to observers and console. Otherwise, only shows explicit
     * echo messages.
     */
    private boolean echoOn = true;

    /**
     * If set to true, an already closed proof leads to an exception if another goal should be
     * picked. Otherwise, script execution terminates without an exception.
     */
    private boolean failOnClosedOn = true;

    public EngineState(Proof proof, ProofScriptEngine engine) {
        this.proof = proof;
        this.engine = engine;
    }

    private ValueInjector createDefaultValueInjector() {
        var v = ValueInjector.createDefault();
        v.addConverter(Term.class, String.class, (str) -> this.toTerm(str, null));
        v.addConverter(Sequent.class, String.class, this::toSequent);
        v.addConverter(Sort.class, String.class, this::toSort);

        addContextTranslator(v, String.class);
        addContextTranslator(v, Term.class);
        addContextTranslator(v, Integer.class);
        addContextTranslator(v, Byte.class);
        addContextTranslator(v, Long.class);
        addContextTranslator(v, Boolean.class);
        addContextTranslator(v, Character.class);
        addContextTranslator(v, Sequent.class);
        addContextTranslator(v, Integer.TYPE);
        addContextTranslator(v, Byte.TYPE);
        addContextTranslator(v, Long.TYPE);
        addContextTranslator(v, Boolean.TYPE);
        addContextTranslator(v, Character.TYPE);
        addContextTranslator(v, Term.class);
        addContextTranslator(v, Sequent.class);
        addContextTranslator(v, Semisequent.class);
        return v;
    }

    private <T> void addContextTranslator(ValueInjector v, Class<T> aClass) {
        Converter<T, ProofScriptExpressionContext> converter =
            (ProofScriptExpressionContext a) -> convertToString(v, aClass, a);
        v.addConverter(aClass, ProofScriptExpressionContext.class, converter);
    }

    @SuppressWarnings("unchecked")
    private <R, T> R convertToString(ValueInjector inj, Class<R> aClass,
            ProofScriptExpressionContext ctx)
            throws Exception {
        try {
            if (aClass == String.class && ctx.string_literal() != null) {
                return inj.getConverter(aClass, String.class)
                        .convert(StringUtil.trim(ctx.string_literal().getText(), '"'));
            }
            if (aClass == String.class) {
                return inj.getConverter(aClass, String.class).convert(ctx.getText());
            }

            T value = (T) ctx.accept(exprEvaluator);
            Class<T> tClass = (Class<T>) value.getClass();
            if (aClass.isAssignableFrom(value.getClass())) {
                return aClass.cast(value);
            }
            return inj.getConverter(aClass, tClass).convert(value);
        } catch (ConversionException | NoSpecifiedConverterException e) {
            return inj.getConverter(aClass, String.class).convert(ctx.getText());
        }
    }

    protected static Goal getGoal(ImmutableList<Goal> openGoals, Node node) {
        for (Goal goal : openGoals) {
            if (goal.node() == node) {
                return goal;
            }
        }
        return null;
    }

    public void setGoal(Goal g) {
        goal = g;
        lastSetGoalNode = Optional.ofNullable(g).map(Goal::node).orElse(null);
    }

    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the first open goal, which has to be automatic iff checkAutomatic is true.
     *
     * @param checkAutomatic Set to true if the returned {@link Goal} should be automatic.
     * @return the first open goal, which has to be automatic iff checkAutomatic
     *         is true.
     * @throws ProofAlreadyClosedException If the proof is already closed when calling this method.
     * @throws ScriptException If there is no such {@link Goal}, or something else goes
     *         wrong.
     */
    @SuppressWarnings("unused")
    public @NonNull Goal getFirstOpenGoal(boolean checkAutomatic) throws ScriptException {
        if (proof.closed()) {
            throw new ProofAlreadyClosedException("The proof is closed already");
        }

        Node rootNodeForSearch = proof.root();
        Goal newGoal = goal;
        if (newGoal != null
                && ((checkAutomatic && !newGoal.isAutomatic()) || newGoal.node().isClosed())) {
            assert rootNodeForSearch != null;
            /*
             * The first subtree of the previous goal is closed. Try with other subtrees.
             */
            rootNodeForSearch = goUpUntilOpen(lastSetGoalNode);
            newGoal = null;
        }

        if (newGoal != null) {
            return newGoal;
        }

        newGoal = findGoalFromRoot(rootNodeForSearch, checkAutomatic);
        if (newGoal == null) {
            throw new ScriptException("There must be an open goal at this point");
        }

        lastSetGoalNode = newGoal.node();

        return newGoal;
    }

    /**
     * @return The first open and automatic {@link Goal}.
     * @throws ScriptException If there is no such {@link Goal}.
     */
    public Goal getFirstOpenAutomaticGoal() throws ScriptException {
        return getFirstOpenGoal(true);
    }

    private static Node goUpUntilOpen(final Node start) {
        Node currNode = start;

        while (currNode.isClosed()) {
            /*
             * There should always be a non-closed parent since we check whether the proof is closed
             * at the beginning.
             */
            currNode = currNode.parent();
        }

        return currNode;
    }

    private Goal findGoalFromRoot(final Node rootNode, boolean checkAutomatic) {
        final Deque<Node> choices = new LinkedList<>();

        Goal result = null;
        Node node = rootNode;

        loop: while (node != null) {
            if (node.isClosed()) {
                return null;
            }

            int childCount = node.childrenCount();

            switch (childCount) {
            case 0 -> {
                result = getGoal(proof.openGoals(), node);
                if (!checkAutomatic || Objects.requireNonNull(result).isAutomatic()) {
                    // We found our goal
                    break loop;
                }
                node = choices.pollLast();
            }
            case 1 -> node = node.child(0);
            default -> {
                Node next = null;
                for (int i = 0; i < childCount; i++) {
                    Node child = node.child(i);
                    if (!child.isClosed()) {
                        if (next == null) {
                            next = child;
                        } else {
                            choices.add(child);
                        }
                    }
                }
                assert next != null;
                node = next;
            }
            }
        }

        return result;
    }


    public Term toTerm(String string, @Nullable Sort sort) throws ParserException, ScriptException {
        final var io = getKeyIO();
        var term = io.parseExpression(string);
        if (sort == null || term.sort().equals(sort))
            return term;
        else
            throw new IllegalStateException(
                "Unexpected sort for term: " + term + ". Expected: " + sort);
    }

    private @NonNull KeyIO getKeyIO() throws ScriptException {
        Services services = proof.getServices();
        KeyIO io = new KeyIO(services, getFirstOpenAutomaticGoal().getLocalNamespaces());
        io.setAbbrevMap(abbrevMap);
        return io;
    }

    public Sort toSort(String sortName) throws ScriptException {
        return (getFirstOpenAutomaticGoal() == null ? getProof().getServices().getNamespaces()
                : getFirstOpenAutomaticGoal().getLocalNamespaces()).sorts().lookup(sortName);
    }

    public Sequent toSequent(String sequent) throws ParserException, ScriptException {
        return getKeyIO().parseSequent(CharStreams.fromString(sequent));
    }

    public int getMaxAutomaticSteps() {
        if (proof != null) {
            return proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    public void setMaxAutomaticSteps(int steps) {
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    public Consumer<ProofScriptEngine.Message> getObserver() {
        return observer;
    }

    public void setObserver(Consumer<ProofScriptEngine.Message> observer) {
        this.observer = observer;
    }

    public Path getBaseFileName() {
        return baseFileName;
    }

    public void setBaseFileName(Path baseFileName) {
        this.baseFileName = baseFileName;
    }

    public ValueInjector getValueInjector() {
        return valueInjector;
    }

    public AbbrevMap getAbbreviations() {
        return abbrevMap;
    }

    public void setGoal(Node node) {
        setGoal(getGoal(proof.openGoals(), node));
    }

    public boolean isEchoOn() {
        return echoOn;
    }

    public void setEchoOn(boolean echoOn) {
        this.echoOn = echoOn;
    }

    public boolean isFailOnClosedOn() {
        return failOnClosedOn;
    }

    public void setFailOnClosedOn(boolean failOnClosedOn) {
        this.failOnClosedOn = failOnClosedOn;
    }

    public ProofScriptEngine getEngine() {
        return engine;
    }

    public NamespaceSet getCurrentNamespaces() {
        try {
            return getFirstOpenAutomaticGoal().getLocalNamespaces();
        } catch (ScriptException e) {
            return proof.getNamespaces();
        }
    }

    public ExprEvaluator getEvaluator() {
        return exprEvaluator;
    }
}
