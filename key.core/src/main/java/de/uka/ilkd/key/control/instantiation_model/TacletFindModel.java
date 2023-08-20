/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control.instantiation_model;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Iterator;
import javax.swing.table.AbstractTableModel;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.NodeOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.IdDeclaration;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.*;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;

import org.antlr.v4.runtime.CharStreams;

public class TacletFindModel extends AbstractTableModel {

    /**
     *
     */
    private static final long serialVersionUID = 5285420522875326156L;
    /** the instantiations entries */
    private final ArrayList<Pair<SchemaVariable, String>> entries;
    /** the related rule application */
    private final TacletApp originalApp;
    /** the integer defines the row until which no editing is possible */
    private int noEditRow;
    /** universal namespace of variables, minimum for input in a row */
    private final NamespaceSet nss;
    /** the java service object */
    private final Services services;
    /** the abbreviation map */
    private final AbbrevMap scm;
    /** the current goal */
    private final Goal goal;
    /** variable namer */
    private final VariableNamer varNamer;
    /** proposers to ask when instantiating a schema variable */
    private final InstantiationProposerCollection instantiationProposers;

    /**
     * Create new data model for tree.
     *
     * @param app the TacletApp where to get the necessary entries
     * @param services services.
     * @param nss universal namespace of variables, minimum for input in a row.
     * @param scm the abbreviation map.
     * @param goal the current goal.
     */
    public TacletFindModel(TacletApp app, Services services, NamespaceSet nss, AbbrevMap scm,
            Goal goal) {
        this.originalApp = app;

        this.nss = nss;
        this.services = services;
        this.scm = scm;
        this.goal = goal;
        this.varNamer = services.getVariableNamer();

        instantiationProposers = new InstantiationProposerCollection();
        instantiationProposers.add(varNamer);
        instantiationProposers.add(VariableNameProposer.DEFAULT);

        entries = createEntryArray(app);
    }

    /**
     * returns the set of namespaces
     */
    private NamespaceSet namespaces() {
        return nss;
    }

    /**
     * creates a Vector with the row entries of the table
     */
    private ArrayList<Pair<SchemaVariable, String>> createEntryArray(TacletApp tacletApp) {
        ArrayList<Pair<SchemaVariable, String>> rowVec = new ArrayList<>();
        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
            tacletApp.instantiations().pairIterator();
        int count = 0;

        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry = it.next();
            rowVec.add(new Pair<>(entry.key(),
                ProofSaver.printAnything(entry.value(), services)));
            count++;
        }

        noEditRow = count - 1;

        ImmutableList<String> proposals = ImmutableSLList.nil();

        for (SchemaVariable var : tacletApp.uninstantiatedVars()) {

            if (!tacletApp.taclet().getIfFindVariables().contains(var)) {
                // create an appropriate and unique proposal for the name ...
                String proposal = instantiationProposers.getProposal(tacletApp, var, services,
                    goal.node(), proposals);

                Pair<SchemaVariable, String> pair = new Pair<>(var, proposal);

                if (proposal != null) {
                    // A proposal is available ...
                    proposals = proposals.append(proposal);
                }

                rowVec.add(pair);
            }
        }

        return rowVec;
    }

    /**
     * number of columns
     *
     * @return number of columns
     */
    @Override
    public int getColumnCount() {
        return 2;
    }

    /**
     * number of rows
     *
     * @return number of rows
     */
    @Override
    public int getRowCount() {
        return entries.size();
    }

    /**
     * returns true iff an instantiation is missing
     *
     * @return true iff an instantiation is missing
     */
    @Override
    public boolean isCellEditable(int rowIndex, int columnIndex) {
        return (rowIndex > noEditRow) && (columnIndex > 0);
    }

    /**
     * parses the given string that represents the term (or formula) using the given variable
     * namespace and the given namespace for functions and default namespaces for the others
     *
     * @param s the String to parse
     * @param varNS the variable namespace
     * @param functNS the function namespace
     */
    private Term parseTerm(String s, Namespace<QuantifiableVariable> varNS,
            Namespace<Function> functNS) throws ParserException {
        NamespaceSet copy = nss.copy();
        copy.setVariables(varNS);
        copy.setFunctions(functNS);
        return new DefaultTermParser().parse(new StringReader(s), null, services, copy, scm);
    }

    /**
     * Parse the declaration of an identifier (i.e. the declaration of a variable or skolem
     * function)
     */
    private IdDeclaration parseIdDeclaration(String s) throws ParserException {
        KeYParser.Id_declarationContext ctx =
            ParsingFacade.parseIdDeclaration(CharStreams.fromString(s));
        Sort sort = ctx.s != null ? services.getNamespaces().sorts().lookup(ctx.s.getText()) : null;
        return new IdDeclaration(ctx.id.getText(), sort);
    }

    private static Position createPosition(int irow) {
        return Position.newOneBased(irow + 1, 1);
    }

    /**
     * throws an exception iff no input in indicated row, and no metavariable instantiation is
     * possible
     *
     */

    private void checkNeededInputAvailable(int irow) throws MissingInstantiationException {

        final int icol = 1;

        if ((getValueAt(irow, icol) == null || ((String) getValueAt(irow, icol)).length() == 0)
                && !originalApp.complete()) {
            throw new MissingInstantiationException(String.valueOf(getValueAt(irow, 0)),
                createPosition(irow),
                false);
        }
    }

    /**
     * @return true iff this row is not empty (i.e. a string of data is available)
     */
    private boolean isInputAvailable(int irow) {
        return getValueAt(irow, 1) != null && ((String) getValueAt(irow, 1)).length() != 0;
    }

    /**
     * parses the indicated row and returns a Term corresponding to the entry in the row
     *
     * @param irow the row to be parsed
     * @param varNS the variable namespace that will be passed to parseTerm
     * @param functNS the function namespace that will be passed to parseTerm
     * @return the parsed term
     */
    private Term parseRow(int irow, Namespace<QuantifiableVariable> varNS,
            Namespace<Function> functNS)
            throws SVInstantiationParserException, MissingInstantiationException {

        String instantiation = (String) getValueAt(irow, 1);

        if (instantiation == null || "".equals(instantiation)) {
            throw new MissingInstantiationException("", createPosition(irow), false);
        }

        try {
            return parseTerm(instantiation, varNS, functNS);
        } catch (ParserException pe) {
            Location loc = pe.getLocation();
            if (loc != null) {
                throw new SVInstantiationParserException(instantiation, loc.getPosition(),
                    pe.getMessage(), false).initCause(pe);
            } else {
                throw new SVInstantiationParserException(instantiation, Position.UNDEFINED,
                    pe.getMessage(), false).initCause(pe);
            }
        }
    }

    /**
     * parses the indicated row and returns a identifier declaration corresponding to the entry in
     * the row
     *
     * @param irow the row to be parsed
     * @return the parsed declaration
     */
    private IdDeclaration parseIdDeclaration(int irow)
            throws SVInstantiationParserException, MissingInstantiationException {

        String instantiation = (String) getValueAt(irow, 1);

        if (instantiation == null || "".equals(instantiation)) {
            throw new MissingInstantiationException("", createPosition(irow), false);
        }

        try {
            return parseIdDeclaration(instantiation);
        } catch (ParserException pe) {
            Location loc = pe.getLocation();
            if (loc != null) {
                throw new SVInstantiationParserException(instantiation,
                    loc.getPosition().offsetLine(irow), pe.getMessage(), false).initCause(pe);
            } else {
                throw new SVInstantiationParserException(instantiation, createPosition(irow),
                    pe.getMessage(), false).initCause(pe);
            }
        }
    }

    private Term addOrigin(Term term) {
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels()) {
            return services.getTermBuilder().addLabelToAllSubs(
                OriginTermLabel.removeOriginLabels(term, services),
                new OriginTermLabel(new NodeOrigin(SpecType.USER_INTERACTION,
                    originalApp.rule().displayName(), goal.node().serialNr())));
        } else {
            return term;
        }
    }

    /**
     * parses the indicated row and returns the ProgramElement corresponding to the entry in the row
     *
     * @param irow the row to be parsed
     * @return the parsed term
     */
    private ProgramElement parseRow(int irow) throws SVInstantiationParserException {

        String instantiation = (String) getValueAt(irow, 1);
        SchemaVariable sv = (SchemaVariable) getValueAt(irow, 0);

        ContextInstantiationEntry contextInstantiation =
            originalApp.instantiations().getContextInstantiation();

        final PosInProgram prefix;
        if (contextInstantiation == null) {
            prefix = PosInProgram.TOP;
        } else {
            prefix = contextInstantiation.prefix();
        }

        if (!varNamer.isUniqueNameForSchemaVariable(instantiation, sv,
            originalApp.posInOccurrence(), prefix)) {
            throw new SVInstantiationParserException(instantiation, createPosition(irow),
                "Name is already in use.", false);
        }

        ProgramElement pe = originalApp.getProgramElement(instantiation, sv, services);
        if (pe == null) {
            throw new SVInstantiationParserException(instantiation, createPosition(irow),
                "Unexpected sort: " + sv.sort() + "." + "Label SV or a program variable SV expected"
                    + " declared as new.",
                false);
        }
        return pe;
    }

    /**
     * @return new rule app with all inserted instantiations in the variable instantiations table
     *
     * @throws SVInstantiationException if the instantiation is incorrect
     */
    public TacletApp createTacletAppFromVarInsts() throws SVInstantiationException {

        final TermBuilder tb = services.getTermBuilder();
        TacletApp result = originalApp;
        SchemaVariable sv = null;
        Sort sort = null;
        int irow = 1;

        try {
            for (irow = noEditRow + 1; irow < entries.size(); irow++) {
                checkNeededInputAvailable(irow);
                sv = (SchemaVariable) getValueAt(irow, 0);
                sort = null;
                if (sv instanceof VariableSV || sv instanceof SkolemTermSV) {
                    IdDeclaration idd = parseIdDeclaration(irow);
                    sort = idd.getSort();
                    if (sort == null) {
                        try {
                            sort = result.getRealSort(sv, services);
                        } catch (SortException e) {
                            throw new MissingSortException(String.valueOf(sv),
                                createPosition(irow));
                        }
                    }

                    if (sv instanceof VariableSV) {
                        LogicVariable lv = new LogicVariable(new Name(idd.getName()), sort);
                        result = result.addCheckedInstantiation(sv, addOrigin(tb.var(lv)), services,
                            true);
                    } else {
                        // sv instanceof SkolemTermSV
                        final Named n = namespaces().lookupLogicSymbol(new Name(idd.getName()));
                        if (n == null) {
                            result = result.createSkolemConstant(idd.getName(), sv, sort, true,
                                services);
                        } else {
                            throw new SVInstantiationParserException(idd.getName(),
                                createPosition(irow),
                                "Name already in use.", false);
                        }
                    }
                } else if (sv instanceof ProgramSV) {
                    final ProgramElement pe = parseRow(irow);
                    result = result.addCheckedInstantiation(sv, pe, services, true);
                }
            }
            SchemaVariable problemVarSV = result.varSVNameConflict();

            if (problemVarSV != null) {
                throw new SVInstantiationParserException("", createPosition(getSVRow(problemVarSV)),
                    "Ambiguous instantiation of schema variable " + problemVarSV, false);
            }

            for (irow = noEditRow + 1; irow < entries.size(); irow++) {

                if (!isInputAvailable(irow)) {
                    continue;
                }

                sv = (SchemaVariable) getValueAt(irow, 0);

                if (sv instanceof VariableSV || sv instanceof SkolemTermSV
                        || result.instantiations().isInstantiated(sv)) {
                    continue;
                }

                sort = null;

                if (sv instanceof ProgramSV) {
                    final ProgramElement pe = parseRow(irow);
                    result = result.addCheckedInstantiation(sv, pe, services, true);
                } else {
                    if (isInputAvailable(irow)) {
                        final Namespace<QuantifiableVariable> extVarNS =
                            result.extendVarNamespaceForSV(nss.variables(), sv);

                        Namespace<Function> functNS =
                            result.extendedFunctionNameSpace(nss.functions());

                        final Term instance = parseRow(irow, extVarNS, functNS);
                        sort = instance.sort();

                        try {
                            result = result.addCheckedInstantiation(sv, addOrigin(instance),
                                services, true);
                        } catch (RigidnessException e) {
                            throw new SVRigidnessException(String.valueOf(sv),
                                createPosition(irow));
                        } catch (IllegalInstantiationException iae) {
                            throw new SVInstantiationParserException((String) getValueAt(irow, 1),
                                createPosition(irow), iae.getMessage(), false);
                        }
                    }
                }
            }
        } catch (SortException e) {
            throw new SortMismatchException(String.valueOf(sv), sort, createPosition(irow));
        }

        return result;

    }

    /** sets the value of the cell */
    @Override
    public void setValueAt(Object instantiation, int rowIndex, int columnIndex) {
        if (columnIndex == 0) {
            entries.set(rowIndex,
                new Pair<>((SchemaVariable) instantiation, entries.get(rowIndex).second));
        } else {
            entries.set(rowIndex, new Pair<>(entries.get(rowIndex).first, (String) instantiation));
        }
    }

    /**
     * get value at the specified row and col
     *
     * @return the value
     */
    @Override
    public Object getValueAt(int row, int col) {
        return col == 0 ? entries.get(row).first : entries.get(row).second;
    }

    /**
     * returns the index of the row the given Schemavariable stands
     *
     * @return the index of the row the given Schemavariable stands (-1 if not found)
     */
    private int getSVRow(SchemaVariable sv) {
        int rowIndex = 0;
        for (Pair<SchemaVariable, String> pair : entries) {
            if (pair.first.equals(sv)) {
                return rowIndex;
            }
            ++rowIndex;
        }
        return -1;
    }

}
