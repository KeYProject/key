/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.visitor.RustyASTVisitor;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.InstantiationProposer;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.NewVarcond;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.rusty.rule.inst.ContextInstantiationEntry;
import org.key_project.util.collection.ImmutableList;


/**
 * Responsible for program variable naming issues.
 */
public abstract class VariableNamer implements InstantiationProposer {
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
    private static boolean suggestiveOff = true;

    /**
     * pointer to services object
     */
    protected final Services services;

    protected final HashMap<ProgramVariable, ProgramVariable> map =
        new LinkedHashMap<>();
    protected HashMap<ProgramVariable, ProgramVariable> renamingHistory =
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

    /**
     * proposes a unique name for the instantiation of a schema variable
     * <p>
     * <strong>Warning:</strong> The current version does not yet guarantee a unique name,
     * but it is very important that this is implemented in the future.
     *
     * @param app the taclet app
     * @param var the schema variable to be instantiated
     * @param services not used
     * @param undoAnchor not used
     * @param previousProposals list of names which should be considered taken, or null
     * @return the name proposal, or null if no proposal is available
     */
    public String getProposal(TacletApp app, org.key_project.logic.op.sv.SchemaVariable var,
            Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        ContextInstantiationEntry cie = app.instantiations().getContextInstantiation();
        PosInProgram posOfDeclaration = (cie == null ? null : cie.prefix());

        NewVarcond nv = (NewVarcond) app.taclet().varDeclaredNew(var);
        // determine a suitable base name
        String basename = null;
        if (nv != null) {
            Type type = nv.getType();
            if (type != null) {
                basename = getBaseNameProposal(type);
            } else {
                org.key_project.logic.op.sv.SchemaVariable psv = nv.getPeerSchemaVariable();
                Object inst = app.instantiations().getInstantiation(psv);
                if (inst instanceof Expr e) {
                    Type ty = e.type(services);
                    basename = getBaseNameProposal(ty);
                } else {
                    // usually this should never be entered, but because of
                    // naming issues we do not want null pointer exceptions
                    // 'u' for unknown
                    basename = "u";
                }
            }
        }
        // get the proposal
        return (getNameProposalForSchemaVariable(basename, var,
            app.posInOccurrence(), posOfDeclaration, previousProposals, services));
    }

    // precondition: sv.sort()==ProgramSVSort.VARIABLE
    public String getSuggestiveNameProposalForProgramVariable(
            org.key_project.logic.op.sv.SchemaVariable sv, TacletApp app,
            Services services, ImmutableList<String> previousProposals) {
        if (suggestiveOff) {
            return getProposal(app, sv, services, null, previousProposals);
        }

        String proposal = "TODO";
        try {
            // TODO
        } catch (Exception e) {
            return getProposal(app, sv, services, null, previousProposals);
        }
        return proposal;
    }

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
    public abstract ProgramVariable rename(ProgramVariable var, Goal goal,
            PosInOccurrence posOfFind);

    public HashMap<ProgramVariable, ProgramVariable> getRenamingMap() {
        return renamingHistory;
    }

    /**
     * proposes a base name for a given sort
     */
    private String getBaseNameProposal(Type type) {
        String result;
        String name = type.name().toString();
        // name = MiscTools.filterAlphabetic(name);
        if (!name.isEmpty()) {
            result = name.substring(0, 1).toLowerCase();
        } else {
            result = "x"; // use default name otherwise
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
    protected String getNameProposalForSchemaVariable(String basename,
            SchemaVariable sv, PosInOccurrence posOfFind, PosInProgram posOfDeclaration,
            ImmutableList<String> previousProposals, Services services) {
        String result = null;

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

                result = tmpName.toString();

                // avoid using a previous proposal again
                if (previousProposals != null) {
                    boolean collision;
                    do {
                        collision = false;
                        for (String previousProposal : previousProposals) {
                            if (previousProposal.equals(result.toString())) {
                                result = basename + ++cnt;
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

    /**
     * returns the maximum counter value already associated with the passed basename in the passed
     * program (ignoring temporary counters), or -1
     */
    protected int getMaxCounterInProgram(String basename, RustyProgramElement program,
            PosInProgram posOfDeclaration) {
        class MyWalker extends CustomRustASTWalker {
            public String basename;
            public int maxCounter = -1;

            public MyWalker(RustyProgramElement program, PosInProgram posOfDeclaration,
                    Services services) {
                super(program, posOfDeclaration, services);
            }

            protected void doAction(RustyProgramElement node) {
                if (node instanceof ProgramVariable var) {
                    Name name = var.name();
                    if (name.toString().equals(basename) && 0 > maxCounter) {
                        maxCounter = 0;
                    } else if (name.toString().contains("_")) {
                        BasenameAndIndex bai = getBasenameAndIndex(name);
                        if (bai != null && bai.basename.equals(basename)
                                && bai.index > maxCounter) {
                            maxCounter = bai.index;
                        }
                    }
                }
            }

            @Override
            protected void doDefaultAction(RustyProgramElement node) {

            }
        }

        MyWalker walker = new MyWalker(program, posOfDeclaration, services);
        walker.basename = basename;
        walker.start();

        return walker.maxCounter;
    }

    /**
     * creates a Globals object for use with other internal methods
     */
    protected Iterable<Name> wrapGlobals(Iterable<? extends Named> globals) {
        List<Name> result = new ArrayList<>();
        for (Named named : globals) {
            result.add(named.name());
        }
        return result;
    }

    /**
     * returns the maximum counter value already associated with the passed basename in the passed
     * list of global variables, or -1
     */
    protected int getMaxCounterInGlobals(String basename, Iterable<Name> globals) {
        int result = -1;

        for (var name : globals) {
            BasenameAndIndex bai = getBasenameAndIndex(name);
            if (bai.basename.equals(basename) && bai.index > result) {
                result = bai.index;
            }
        }

        return result;
    }

    /**
     * tells whether a name is unique in the passed list of global variables
     */
    protected boolean isUniqueInGlobals(String name, Iterable<Name> globals) {
        for (var n : globals) {
            if (n.toString().equals(name)) {
                return false;
            }
        }
        return true;
    }

    /**
     * proposes a unique name; intended for use in places where the information required by
     * getProposal() is not available
     *
     * @param basename desired base name, or null to use default
     * @return the name proposal
     */
    public Name getTemporaryNameProposal(String basename) {
        if (basename == null || basename.isEmpty()) {
            basename = DEFAULT_BASENAME;
        }
        int cnt = services.getCounter(TEMPCOUNTER_NAME).getCountPlusPlus();
        return new Name(basename + (cnt == 0 ? "" : "_" + cnt));
    }

    /**
     * a customized RustASTWalker
     */
    private abstract static class CustomRustASTWalker extends RustyASTVisitor {
        private RustyProgramElement declarationNode = null;
        private int declarationScopeDepth = -2;
        private int currentScopeDepth = -2;

        CustomRustASTWalker(RustyProgramElement program, PosInProgram posOfDeclaration,
                Services services) {
            super(program, services);
            if (posOfDeclaration != null) {
                declarationNode = PosInProgram.getProgramAt(posOfDeclaration, program);
            }
        }

        protected void walk(RustyProgramElement node) {
            if (node instanceof BlockExpression) {
                currentScopeDepth = depth();
            } else if (node == declarationNode) {
                declarationScopeDepth = currentScopeDepth;
            } else if (depth() <= declarationScopeDepth) {
                return;
            }

            super.walk(node);
        }
    }

    protected BasenameAndIndex getBasenameAndIndex(Name name) {
        String s = name.toString();
        var splits = s.split("_");
        try {
            String last = splits[splits.length - 1];
            int idx = Integer.parseInt(last);
            var base = s.substring(0, s.length() - last.length() - 1);
            return new BasenameAndIndex(base, idx);
        } catch (NumberFormatException e) {
            return new BasenameAndIndex(s, 0);
        }
    }

    /**
     * returns the program contained in a PosInOccurrence
     */
    protected RustyProgramElement getProgramFromPIO(PosInOccurrence pio) {
        Term progTerm;
        if (pio != null && (progTerm = findProgramInTerm(pio.subTerm())) != null) {
            var mod = (Modality) progTerm.op();
            return mod.program().program();
        } else {
            return new EmptyStatement();
        }
    }

    /**
     * returns the subterm containing a java block, or null (helper for getProgramFromPIO())
     */
    private Term findProgramInTerm(Term term) {
        if (term.op() instanceof Modality) {
            return term;
        }
        for (int i = 0; i < term.arity(); i++) {
            Term subterm = findProgramInTerm(term.sub(i));
            if (subterm != null) {
                return subterm;
            }
        }
        return null;
    }

    protected record BasenameAndIndex(String basename, int index) {}
}
