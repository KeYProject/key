/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InstantiationProposer;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Responsible for program variable naming issues.
 */
public abstract class VariableNamer implements InstantiationProposer {
    /**
     * Separator used for {@link TempIndProgramElementName} instances.
     * This will separate the name and the index of the "temporary"
     * program element name.
     */
    public static final char TEMP_INDEX_SEPARATOR = '#';

    private static final Logger LOGGER = LoggerFactory.getLogger(VariableNamer.class);

    // -------------------------------------------------------------------------
    // member variables
    // -------------------------------------------------------------------------

    /**
     * default basename for variable name proposals
     */
    private static final String DEFAULT_BASENAME = "var";


    /**
     * name of the counter object used for temporary name proposals
     */
    private static final String TEMPCOUNTER_NAME = "VarNamerCnt";



    /**
     * status of suggestive name proposing
     */
    private static boolean suggestive_off = true;


    /**
     * pointer to services object
     */
    protected final Services services;

    protected final HashMap<LocationVariable, LocationVariable> map =
        new LinkedHashMap<>();
    protected HashMap<LocationVariable, LocationVariable> renamingHistory =
        new LinkedHashMap<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * @param services pointer to services object
     */
    protected VariableNamer(Services services) {
        this.services = services;
    }



    // -------------------------------------------------------------------------
    // internal: general stuff
    // -------------------------------------------------------------------------

    /**
     * determines the passed ProgramElementName's basename and index (ignoring temporary indices)
     */
    protected BasenameAndIndex getBasenameAndIndex(ProgramElementName name) {
        BasenameAndIndex result = new BasenameAndIndex();

        if (name instanceof PermIndProgramElementName) {
            result.basename = ((IndProgramElementName) name).getBaseName();
            result.index = ((IndProgramElementName) name).getIndex();
        } else if (name instanceof TempIndProgramElementName) {
            result.basename = ((IndProgramElementName) name).getBaseName();
            result.index = 0;
        } else {
            result.basename = name.toString();
            result.index = 0;
        }

        return result;
    }


    public HashMap<LocationVariable, LocationVariable> getRenamingMap() {
        return renamingHistory;
    }

    /**
     * returns the subterm containing a java block, or null (helper for getProgramFromPIO())
     */
    private JTerm findProgramInTerm(JTerm term) {
        if (!term.javaBlock().isEmpty()) {
            return term;
        }
        for (int i = 0; i < term.arity(); i++) {
            JTerm subterm = findProgramInTerm(term.sub(i));
            if (subterm != null) {
                return subterm;
            }
        }
        return null;
    }


    /**
     * returns the program contained in a PosInOccurrence
     */
    protected ProgramElement getProgramFromPIO(PosInOccurrence pio) {
        JTerm progTerm;
        if (pio != null && (progTerm = findProgramInTerm((JTerm) pio.subTerm())) != null) {
            return progTerm.javaBlock().program();
        } else {
            return new EmptyStatement();
        }
    }


    /**
     * creates a ProgramElementName object to be used for permanent names
     */
    protected ProgramElementName createName(String basename, int index,
            NameCreationInfo creationInfo) {
        return new PermIndProgramElementName(basename, index, creationInfo);
    }



    // -------------------------------------------------------------------------
    // internal: counter finding
    // -------------------------------------------------------------------------

    /**
     * returns the maximum counter value already associated with the passed basename in the passed
     * list of global variables, or -1
     */
    protected int getMaxCounterInGlobals(String basename, Iterable<ProgramElementName> globals) {
        int result = -1;

        for (ProgramElementName name : globals) {
            BasenameAndIndex bai = getBasenameAndIndex(name);
            if (bai.basename.equals(basename) && bai.index > result) {
                result = bai.index;
            }
        }

        return result;
    }


    /**
     * returns the maximum counter value already associated with the passed basename in the passed
     * program (ignoring temporary counters), or -1
     */
    protected int getMaxCounterInProgram(String basename, ProgramElement program,
            PosInProgram posOfDeclaration) {
        class MyWalker extends CustomJavaASTWalker {
            public String basename;
            public int maxCounter = -1;

            public MyWalker(ProgramElement program, PosInProgram posOfDeclaration) {
                super(program, posOfDeclaration);
            }

            protected void doAction(ProgramElement node) {
                if (node instanceof ProgramVariable var) {
                    ProgramElementName name = var.getProgramElementName();
                    if (!(name instanceof TempIndProgramElementName)) {
                        BasenameAndIndex bai = getBasenameAndIndex(name);
                        if (bai.basename.equals(basename) && bai.index > maxCounter) {
                            maxCounter = bai.index;
                        }
                    }
                }
            }
        }

        MyWalker walker = new MyWalker(program, posOfDeclaration);
        walker.basename = basename;
        walker.start();

        return walker.maxCounter;
    }



    // -------------------------------------------------------------------------
    // internal: uniqueness checking
    // -------------------------------------------------------------------------

    /**
     * tells whether a name is unique in the passed list of global variables
     */
    protected boolean isUniqueInGlobals(String name, Iterable<ProgramElementName> globals) {
        for (ProgramElementName n : globals) {
            if (n.toString().equals(name)) {
                return false;
            }
        }
        return true;
    }


    /**
     * tells whether a name is unique in the passed program
     */
    protected boolean isUniqueInProgram(String name, ProgramElement program,
            PosInProgram posOfDeclaration) {
        class MyWalker extends CustomJavaASTWalker {
            public String nameToFind;
            public boolean foundIt = false;

            public MyWalker(ProgramElement program, PosInProgram posOfDeclaration) {
                super(program, posOfDeclaration);
            }

            protected void doAction(ProgramElement node) {
                if (node instanceof ProgramVariable var) {
                    ProgramElementName varname = var.getProgramElementName();
                    if (varname.getProgramName().equals(nameToFind)) {
                        foundIt = true;
                    }
                }
            }
        }

        MyWalker walker = new MyWalker(program, posOfDeclaration);
        walker.nameToFind = name;
        walker.start();

        return !walker.foundIt;
    }



    // -------------------------------------------------------------------------
    // internal: uniform treatment of global variables
    // -------------------------------------------------------------------------

    /**
     * creates a Globals object for use with other internal methods
     */
    protected Iterable<ProgramElementName> wrapGlobals(Iterable<? extends Named> globals) {
        List<ProgramElementName> result = new ArrayList<>();
        for (Named named : globals) {
            result.add((ProgramElementName) named.name());
        }
        return result;
    }

    // -------------------------------------------------------------------------
    // interface: renaming
    // -------------------------------------------------------------------------

    /**
     * intended to be called when symbolically executing a variable declaration; resolves any naming
     * conflicts between the new variable and other global variables by renaming the new variable
     * and / or other variables
     *
     * @param var the new program variable
     * @param goal the goal
     * @param posOfFind the PosInOccurrence of the currently executed program
     * @return the renamed version of the var parameter
     */
    public abstract LocationVariable rename(LocationVariable var, Goal goal,
            PosInOccurrence posOfFind);



    // -------------------------------------------------------------------------
    // internal: name proposals
    // -------------------------------------------------------------------------

    /**
     * proposes a base name for a given sort
     */
    private String getBaseNameProposal(Type type) {
        String result;
        if (type instanceof ArrayType) {
            result = getBaseNameProposal(
                ((ArrayType) type).getBaseType().getKeYJavaType().getJavaType());
            result += "_arr";
        } else {
            String name = type.getName();
            name = MiscTools.filterAlphabetic(name);
            if (!name.isEmpty()) {
                result = name.substring(0, 1).toLowerCase();
            } else {
                result = "x"; // use default name otherwise
            }
        }

        return result;
    }


    /**
     * proposes a unique name for the instantiation of a schema variable (like getProposal(), but
     * somewhat less nicely)
     *
     * @param basename desired base name, or null to use default
     * @param sv the schema variable
     * @param posOfFind the PosInOccurrence containing the name's target program
     * @param posOfDeclaration the PosInProgram where the name will be declared (or null to just be
     *        pessimistic about the scope)
     * @param previousProposals list of names which should be considered taken, or null
     * @return the name proposal, or null if no proposal is available
     */
    protected ProgramElementName getNameProposalForSchemaVariable(String basename,
            SchemaVariable sv, PosInOccurrence posOfFind,
            PosInProgram posOfDeclaration,
            ImmutableList<String> previousProposals, Services services) {
        ProgramElementName result = null;

        if (sv instanceof ProgramSV psv) {
            Sort svSort = psv.sort();

            if (svSort == ProgramSVSort.VARIABLE) {
                if (basename == null || basename.isEmpty()) {
                    basename = DEFAULT_BASENAME;
                }
                int cnt =
                    getMaxCounterInProgram(basename, getProgramFromPIO(posOfFind), posOfDeclaration)
                            + 1;

                Name tmpName = new Name(basename + (cnt == 0 ? "" : "_" + cnt));
                while (services.getNamespaces().lookupLogicSymbol(tmpName) != null) {
                    cnt++;
                    tmpName = new Name(basename + "_" + cnt);
                }

                result = createName(basename, cnt, null);

                // avoid using a previous proposal again
                if (previousProposals != null) {
                    boolean collision;
                    do {
                        collision = false;
                        for (String previousProposal : previousProposals) {
                            if (previousProposal.equals(result.toString())) {
                                result = createName(basename, ++cnt, null);
                                collision = true;
                                break;
                            }
                        }
                    } while (collision);
                }
            }
        }

        return result;
    }



    // -------------------------------------------------------------------------
    // interface: name proposals
    // -------------------------------------------------------------------------

    /**
     * proposes a unique name; intended for use in places where the information required by
     * getProposal() is not available
     *
     * @param basename desired base name, or null to use default
     * @return the name proposal
     */
    public ProgramElementName getTemporaryNameProposal(String basename) {
        if (basename == null || basename.isEmpty()) {
            basename = DEFAULT_BASENAME;
        }
        int cnt = services.getCounter(TEMPCOUNTER_NAME).getCountPlusPlus();
        // using null as undo anchor should be okay, since the name which the
        // the counter is used for is only temporary and will be changed
        // before the variable enters the logic

        return new TempIndProgramElementName(basename, cnt, null);
    }


    /**
     * proposes a unique name for the instantiation of a schema variable
     *
     * @param app the taclet app
     * @param var the schema variable to be instantiated
     * @param services not used
     * @param undoAnchor not used
     * @param previousProposals list of names which should be considered taken, or null
     * @return the name proposal, or null if no proposal is available
     */
    @Override
    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        // determine posOfDeclaration from TacletApp
        ContextStatementBlockInstantiation cie = app.instantiations().getContextInstantiation();
        PosInProgram posOfDeclaration = (cie == null ? null : cie.prefix());

        // determine a suitable base name
        String basename = null;
        NewVarcond nv =
            (NewVarcond) app.taclet().varDeclaredNew(var);
        if (nv != null) {
            Type type = nv.getType();
            if (type != null) {
                basename = getBaseNameProposal(type);
            } else {
                SchemaVariable psv = nv.getPeerSchemaVariable();
                Object inst = app.instantiations().getInstantiation(psv);
                if (inst instanceof Expression) {
                    final ExecutionContext ec = app.instantiations().getExecutionContext();
                    if (ec != null) {
                        KeYJavaType kjt = ((Expression) inst).getKeYJavaType(this.services, ec);
                        basename = getBaseNameProposal(kjt.getJavaType());
                    } else {
                        // usually this should never be entered, but because of
                        // naming issues we do not want nullpointer exceptions
                        // 'u' for unknown
                        basename = "u";
                    }
                }
            }
        }

        // get the proposal
        ProgramElementName name = getNameProposalForSchemaVariable(basename, var,
            app.posInOccurrence(), posOfDeclaration, previousProposals, services);
        return (name == null ? null : name.toString());
    }



    // -------------------------------------------------------------------------
    // interface: uniqueness checking
    // -------------------------------------------------------------------------

    /**
     * tells whether a name for instantiating a schema variable is unique within its scope
     *
     * @param name the name to be checked
     * @param sv the schema variable
     * @param posOfFind the PosInOccurrence of the name's target program
     * @param posOfDeclaration the PosInProgram where the name will be declared
     * @return true if the name is unique or if its uniqueness cannot be checked, else false
     */
    public boolean isUniqueNameForSchemaVariable(String name, ProgramSV sv,
            PosInOccurrence posOfFind, PosInProgram posOfDeclaration) {
        boolean result = true;

        Sort svSort = sv.sort();
        if (svSort == ProgramSVSort.VARIABLE) {
            result = isUniqueInProgram(name, getProgramFromPIO(posOfFind), posOfDeclaration);
        }

        return result;
    }



    // -------------------------------------------------------------------------
    // interface: name parsing
    // -------------------------------------------------------------------------

    /**
     * parses the passed string and creates a suitable program element name (this does *not* make
     * the name unique - if that is necessary, use either getTemporaryNameProposal() or
     * getProposal())
     *
     * @param name the name as a string
     * @param creationInfo optional name creation info the name should carry
     * @param comments any comments the name should carry
     * @return the name as a ProgramElementName
     */
    public static ProgramElementName parseName(String name, NameCreationInfo creationInfo,
            Comment[] comments) {
        ProgramElementName result;

        int sepPos = name.lastIndexOf(TEMP_INDEX_SEPARATOR);
        if (sepPos > 0) {
            String basename = name.substring(0, sepPos);
            int index = Integer.parseInt(name.substring(sepPos + 1));
            result = new TempIndProgramElementName(basename, index, creationInfo, comments);
        } else {
            sepPos = name.lastIndexOf(PermIndProgramElementName.SEPARATOR);
            if (sepPos > 0) {
                try {
                    String basename = name.substring(0, sepPos);
                    int index = Integer.parseInt(name.substring(sepPos + 1));
                    result = new PermIndProgramElementName(basename, index, creationInfo, comments);
                } catch (NumberFormatException e) {
                    result = new ProgramElementName(name, creationInfo, comments);
                }
            } else {
                result = new ProgramElementName(name, creationInfo, comments);
            }
        }

        return result;
    }


    public static ProgramElementName parseName(String name, NameCreationInfo creationInfo) {
        return parseName(name, creationInfo, new Comment[0]);
    }


    public static ProgramElementName parseName(String name, Comment[] comments) {
        return parseName(name, null, comments);
    }


    public static ProgramElementName parseName(String name) {
        return parseName(name, null, new Comment[0]);
    }



    // -------------------------------------------------------------------------
    // interface: suggestive name proposals
    // (taken from VarNameDeliverer.java, pretty much unchanged)
    // -------------------------------------------------------------------------

    public static void setSuggestiveEnabled(boolean enabled) {
        suggestive_off = !enabled;
    }


    // precondition: sv.sort()==ProgramSVSort.VARIABLE
    public String getSuggestiveNameProposalForProgramVariable(SchemaVariable sv, TacletApp app,
            Services services, ImmutableList<String> previousProposals) {

        if (suggestive_off) {
            return getProposal(app, sv, services, null, previousProposals);
        }

        String proposal;
        try {
            var templs = app.taclet().goalTemplates().iterator();
            RewriteTacletGoalTemplate rwgt;
            String name = "";
            while (templs.hasNext()) {
                rwgt = (RewriteTacletGoalTemplate) templs.next();
                JTerm t = findProgramInTerm(rwgt.replaceWith());
                ContextStatementBlock c = (ContextStatementBlock) t.javaBlock().program();
                if (c.getStatementAt(0) instanceof LocalVariableDeclaration) {
                    VariableSpecification v =
                        ((LocalVariableDeclaration) c.getStatementAt(0)).getVariables().get(0);

                    if (v.hasInitializer()) {
                        ProgramElement rhs = instantiateExpression(v.getInitializer(),
                            app.instantiations(), services);
                        name = ProofSaver.printProgramElement(rhs);
                        break;
                    } else if (c.getStatementAt(1) instanceof CopyAssignment p2) {
                        Expression lhs = p2.getExpressionAt(0);
                        if (lhs.equals(sv)) {
                            SchemaVariable rhs = (SchemaVariable) p2.getExpressionAt(1);
                            name = app.instantiations().getInstantiation(rhs).toString();
                            break;
                        }
                    }
                }

            }
            if ("".equals(name)) {
                throw new Exception();
            }
            proposal = "[" + name + "]";
        } catch (Exception e) {
            LOGGER.info("", e);
            return getProposal(app, sv, services, null, previousProposals);
        }
        return proposal;
    }


    public String getSuggestiveNameProposalForSchemaVariable(Expression e) {
        if (suggestive_off) {
            return getTemporaryNameProposal(DEFAULT_BASENAME).toString();
        }
        return "[" + ProofSaver.printProgramElement(e) + "]";
    }



    private ProgramElement instantiateExpression(ProgramElement e, SVInstantiations svInst,
            Services services) {
        ProgramReplaceVisitor trans = new ProgramReplaceVisitor(e, services, svInst);
        trans.start();
        return trans.result();
    }



    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    /**
     * ProgramElementName carrying an additional index
     */
    public abstract static class IndProgramElementName extends ProgramElementName {
        private final String basename;
        private final int index;

        IndProgramElementName(String name, String basename, int index,
                NameCreationInfo creationInfo) {
            super(name, creationInfo);
            this.basename = basename.intern();
            this.index = index;
        }

        IndProgramElementName(String name, String basename, int index,
                NameCreationInfo creationInfo, Comment[] comments) {
            super(name, creationInfo, comments);
            this.basename = basename.intern();
            this.index = index;
        }

        public String getBaseName() {
            return basename;
        }

        public int getIndex() {
            return index;
        }
    }


    /**
     * temporary indexed ProgramElementName
     */
    private static class TempIndProgramElementName extends IndProgramElementName {
        TempIndProgramElementName(String basename, int index, NameCreationInfo creationInfo) {
            super(basename + TEMP_INDEX_SEPARATOR + index, basename, index, creationInfo);
        }

        TempIndProgramElementName(String basename, int index, NameCreationInfo creationInfo,
                Comment[] comments) {
            super(basename + TEMP_INDEX_SEPARATOR + index, basename, index, creationInfo,
                comments);
        }
    }


    /**
     * regular indexed ProgramElementName
     */
    private static class PermIndProgramElementName extends IndProgramElementName {
        static final char SEPARATOR = '_';

        PermIndProgramElementName(String basename, int index, NameCreationInfo creationInfo) {
            super(basename + (index == 0 ? "" : SEPARATOR + String.valueOf(index)), basename, index,
                creationInfo);
        }

        PermIndProgramElementName(String basename, int index, NameCreationInfo creationInfo,
                Comment[] comments) {
            super(basename + (index == 0 ? "" : SEPARATOR + String.valueOf(index)), basename, index,
                creationInfo, comments);
        }
    }

    /**
     * a customized JavaASTWalker
     */
    private abstract static class CustomJavaASTWalker extends JavaASTWalker {
        private ProgramElement declarationNode = null;
        private int declarationScopeDepth = -2;
        private int currentScopeDepth = -2;

        CustomJavaASTWalker(ProgramElement program, PosInProgram posOfDeclaration) {
            super(program);
            if (posOfDeclaration != null) {
                declarationNode = PosInProgram.getProgramAt(posOfDeclaration, program);
            }
        }

        protected void walk(ProgramElement node) {
            // ignore ExecutionContext and IProgramMethod branches;
            // ignore anything rooted at a depth less or equal than the depth
            // of the scope containing the declaration (except for this
            // "declaration scope" itself);
            if (node instanceof ExecutionContext || node instanceof IProgramMethod) {
                return;
            } else if (node instanceof ScopeDefiningElement) {
                currentScopeDepth = depth();
            } else if (node == declarationNode) {
                declarationScopeDepth = currentScopeDepth;
            } else if (depth() <= declarationScopeDepth) {
                return;
            }

            super.walk(node);
        }
    }


    /**
     * tuple of a basename and an index
     */
    protected static class BasenameAndIndex {
        public String basename;
        public int index;
    }

    public static Name getBasename(Name name) {
        if (name instanceof IndProgramElementName) {
            return new Name(((IndProgramElementName) name).getBaseName());
        }
        return name;
    }
}
