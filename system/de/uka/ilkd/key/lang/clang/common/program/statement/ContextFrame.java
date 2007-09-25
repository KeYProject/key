package de.uka.ilkd.key.lang.clang.common.program.statement;

import java.util.Set;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.util.PatternUtil;
import de.uka.ilkd.key.lang.common.match.IKeyedMatchPatternProgramElement;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.ISchemaProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.util.ExtList;

/**
 * In the DL-formulae description of Taclets the program part can have the
 * following form < pi alpha;...; omega > Phi where pi is a prefix consisting of
 * frames and omega is the rest of the program. Between the prefix pi and the
 * postfix omega there can stand an arbitrary program. This pattern is realized
 * using this class.
 */
public final class ContextFrame extends BaseClangStatement implements
                IKeyedMatchPatternProgramElement, ISchemaProgramElement {

        private final ArrayOfIClangStatement statements;

        public ContextFrame(ArrayOfIClangStatement statements) {
                this.statements = statements;
        }

        public ContextFrame(ExtList children, ContextFrame original) {
                super(children);
                statements = new ArrayOfIClangStatement(
                                (IClangStatement[]) children
                                                .collect(IClangStatement.class));
        }
        
        public IProgramElement copy(ExtList children) {
                return new ContextFrame(children, this);
        }
        
        public int getChildCount() {
                return statements.size();
        }

        public IProgramElement getProgramElementAt(int index) {
                return statements.getIClangStatement(index);
        }

        public ArrayOfIClangStatement getStatements() {
                return statements;
        }

        public int getStatementCount() {
                return statements.size();
        }

        public IClangStatement getStatementAt(int index) {
                return statements.getIClangStatement(index);
        }

        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchContextFrame(this);
        }

        public void addMatchPatternKeys(Set set) {
                if (getStatementCount() > 0) {
                        IClangStatement statement = getStatementAt(0);
                        if (statement instanceof IKeyedMatchPatternProgramElement)
                                ((IKeyedMatchPatternProgramElement) statement)
                                                .addMatchPatternKeys(set);
                        else
                                set.add(PatternUtil.buildKey(statement));
                } else
                        // Pattern ".. ..." should never match
                        set.add(PatternUtil.NON_EXISTENT_KEY);
        }

        public static final SchemaVariable CONTEXTSV = new BaseProgramSV(
                        new Name("ClangContext"), new BaseProgramSVSort(
                                        new Name("ContextFrame")) {
                                public boolean canStandFor(IProgramElement pe,
                                                ILangServices services,
                                                Namespace sortNS,
                                                Namespace symbolNS) {
                                        throw new IllegalStateException(
                                                "This program SV sort cannot be used to match program elements directly.");
                                }

                                public BaseProgramSV buildProgramSV(Name name) {
                                        throw new IllegalStateException(
                                                        "This program SV sort cannot be used to create new program SVs.");
                                }
                        }) {
                public IProgramPrinter createDefaultPrinter() {
                        return new ClangProgramPrinter();
                }
        };

        public static class ContextInstantiation {
                private RootFrame environment;

                private int depth;

                private int size;

                public ContextInstantiation(RootFrame environment, int depth,
                                int size) {
                        this.environment = environment;
                        this.depth = depth;
                        this.size = size;
                }

                public RootFrame getContext() {
                        return environment;
                }

                public int getDepth() {
                        return depth;
                }

                public int getSize() {
                        return size;
                }
        }

        public static class ContextInstantiationEntry extends
                        InstantiationEntry {
                private ContextInstantiation instantiation;

                public ContextInstantiationEntry(
                                ContextInstantiation instantiation) {
                        super(CONTEXTSV);
                        this.instantiation = instantiation;
                }

                public Object getInstantiation() {
                        return instantiation;
                }

                public String toString() {
                        return "[" + getSchemaVariable() + ",\\depth:"
                                        + instantiation.getDepth() + "\\size"
                                        + instantiation.getSize() + "\n]";
                }

        }

        public MatchConditions match(SourceData sourceData,
                        MatchConditions matchCond) {
                ProgramElement source = sourceData.getSource();
                if (!(source instanceof RootFrame))
                        return null;
                RootFrame rootFrame = (RootFrame) source;
                MatchConditions newMatchCond = matchFrameBody(rootFrame,
                                rootFrame.getBody(), matchCond, sourceData
                                                .getServices());
                if (newMatchCond != null) {
                        ContextInstantiation inst = ((ContextInstantiation) newMatchCond
                                        .getInstantiations()
                                        .getInstantiationEntry(CONTEXTSV)
                                        .getInstantiation());
                        inst.environment = rootFrame;
                        return newMatchCond;
                } else
                        return null;

        }

        public MatchConditions matchFrameBody(ProgramElement environment,
                        FrameBody body, MatchConditions matchCond,
                        Services services) {
                // Empty statement list cannot match
                if (body.getStatementCount() == 0)
                        return null;

                // Try descending into the first statement
                IClangStatement firstStatement = body.getStatementAt(0);
                FrameBody newFrameBody = null;
                if (firstStatement instanceof BlockFrame)
                        newFrameBody = ((BlockFrame) firstStatement).getBody();
                if (newFrameBody != null) {
                        MatchConditions newMatchCond = matchFrameBody(
                                        firstStatement, newFrameBody,
                                        matchCond, services);
                        if (newMatchCond != null) {
                                ContextInstantiation inst = ((ContextInstantiation) newMatchCond
                                                .getInstantiations()
                                                .getInstantiationEntry(
                                                                CONTEXTSV)
                                                .getInstantiation());
                                inst.depth++;
                                return newMatchCond;
                        }
                }

                // If the body does not have enough statements to match
                if (body.getStatementCount() < getStatementCount())
                        return null;

                // Try matching the first elements
                MatchConditions newMatchCond = matchCond;
                for (int i = 0; i < getStatementCount(); i++) {
                        SourceData sourceData = new SourceData(body
                                        .getStatementAt(i), -1, services);
                        newMatchCond = getStatementAt(i).match(sourceData,
                                        newMatchCond);
                        if (newMatchCond == null)
                                return null;
                }

                return newMatchCond
                                .setInstantiations(newMatchCond
                                                .getInstantiations()
                                                .add(
                                                                CONTEXTSV,
                                                                new ContextInstantiationEntry(
                                                                                new ContextInstantiation(
                                                                                                null,
                                                                                                0,
                                                                                                getStatementCount()))));
        }

        public IProgramElement instantiate(ContextInstantiation inst) {
                return new RootFrame(instantiateFrameBody(inst.getContext()
                                .getBody(), inst.getDepth(), inst.getSize()));
        }

        public FrameBody instantiateFrameBody(FrameBody body, int depth,
                        int size) {
                if (depth == 0) {
                        // Fill in environment
                        int bodyStatementCount = body.getStatementCount();
                        int environmentStatementCount = getStatementCount();
                        IClangStatement[] newStatements = new IClangStatement[bodyStatementCount
                                        - size + environmentStatementCount];
                        this.getStatements().arraycopy(0, newStatements, 0,
                                        environmentStatementCount);
                        body.getStatements().arraycopy(size, newStatements,
                                        environmentStatementCount,
                                        bodyStatementCount - size);
                        return new FrameBody(new ArrayOfIClangStatement(
                                        newStatements));
                }

                // Instantiate first statement
                IClangStatement firstStatement = body.getStatementAt(0);
                IClangStatement newFirstStatement = null;
                if (firstStatement instanceof BlockFrame) {
                        BlockFrame blockFrame = (BlockFrame) firstStatement;
                        newFirstStatement = new BlockFrame(blockFrame
                                        .getVariables(), instantiateFrameBody(
                                        blockFrame.getBody(), depth - 1, size));
                }
                assert newFirstStatement != null;

                // Replace the first statement
                int bodyStatementCount = body.getStatementCount();
                IClangStatement[] newStatements = new IClangStatement[bodyStatementCount];
                newStatements[0] = newFirstStatement;
                body.getStatements().arraycopy(1, newStatements, 1,
                                bodyStatementCount - 1);
                return new FrameBody(new ArrayOfIClangStatement(newStatements));
        }

}
