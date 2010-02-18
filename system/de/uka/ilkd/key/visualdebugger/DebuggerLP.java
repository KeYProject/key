// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObject;

public class DebuggerLP extends LogicPrinter {
    
    private Abb abb = new Abb();

    private NotationInfo info;

    private HashMap inputValues;

    private List<SymbolicObject> objects;

    private Services services;

    private SymbolicObject thisObject;

    final VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public DebuggerLP(ProgramPrinter prgPrinter, NotationInfo notationInfo,
            Services services, HashMap inputValues) {
        super(prgPrinter, notationInfo, services);
        // TODO Auto-generated constructor stub
        notationInfo.setAbbrevMap(new AbbrevMap());
        info = notationInfo;
        this.objects = new LinkedList<SymbolicObject>();
        this.inputValues = inputValues;
        this.services = services;

    }

    public DebuggerLP(ProgramPrinter prgPrinter, NotationInfo notationInfo,
            Services services, HashMap inputValues, List<SymbolicObject> objects,
            SymbolicObject thisObject) {
        super(prgPrinter, notationInfo, services);
        info = notationInfo;
        this.objects = objects;
        this.thisObject = thisObject;
        this.inputValues = inputValues;
        this.services = services;
        this.createAb();
    }

    private void createAb() {
        for (final SymbolicObject so : objects) {
            for (final Term t : so.getTerms()) {
                try {
                    if (so != thisObject) {
                        if (!abb.containsTerm(t))
                            abb.put(t, so.getInstanceName(), true);
                    } else if (!abb.containsTerm(t))
                        abb.put(t, "this", true);
                } catch (AbbrevException e) {
                    e.printStackTrace();
                }
            }

        }
        info.setAbbrevMap(abb);
    }

    private String getName(Term t) {
        for (final SymbolicObject so : objects) {
            if (so.getTerms().contains(t)) {
                return so.getInstanceName();
            }
        }
        return null;
    }

    public void printCast(String pre, String post, Term t, int ass)
            throws IOException {
        printTerm(t.sub(0));
    }

    public void printTerm(Term t) throws IOException {
        if (getNotationInfo().getAbbrevMap().isEnabled(t)) {
            startTerm(0);
            layouter.print(getNotationInfo().getAbbrevMap().getAbbrev(t));
        } else {
            String s = this.getName(t);
            if (s != null) {
                startTerm(0);
                layouter.print(s);
            } else

            if (inputValues.containsKey(t)) {
                startTerm(0);
                final Term it = (Term) inputValues.get(t);

                if ((!vd.isStaticMethod() && !vd.getSelfTerm().equals(it))
                        || vd.isStaticMethod())
                    layouter.print(it.toString() + "_i");
                // else if (vd.isStaticMethod());
                else
                    layouter.print(it.toString());
            } else {
                if (t.op() instanceof SortDependingFunction
                        && t.op().name().toString()
                                .endsWith("<get>")) {
                    Term sub = t.sub(0);
                    if (sub.arity() > 1)
                        layouter
                                .print("new" + t.sort() + sub.sub(0).toString());
                    else
                        layouter.print("new" + t.sort() + "0");
                } else

                    getNotationInfo().getNotation(t.op(), services).print(t,
                            this);
            }
        }
    }

    class Abb extends AbbrevMap {

        // public String getAbbrev(Term t){
        // return super.getAbbrev(t).substring(1);
        // }

        /**
         * Changes the abbreviation of t to abbreviation. If the AbbrevMap
         * doesn't contain t nothing happens.
         */
        public void changeAbbrev(Term t, String abbreviation)
                throws AbbrevException {
            if (containsTerm(t)) {
                AbbrevWrapper scw;
                // if(containsAbbreviation(abbreviation)){
                // throw new AbbrevException("The abbreviation "+abbreviation+"
                // is already"+
                // " in use for: "+getTerm(abbreviation),false);
                // }
                scw = new AbbrevWrapper(t);
                stringterm.remove(termstring.get(scw));
                termstring.put(scw, abbreviation);
                stringterm.put(abbreviation, scw);
            }
        }

        /**
         * Returns true if the map contains the abbreviation s.
         */
        public boolean containsAbbreviation(String s) {
            return stringterm.containsKey(s);
        }

        /**
         * Returns true if the map contains the term t.
         */
        public boolean containsTerm(Term t) {
            return termstring.containsKey(new AbbrevWrapper(t));
        }

        /**
         * Returns the abbreviation mapped to the term t. Returns null if no
         * abbreviation is mapped to t.
         */
        public String getAbbrev(Term t) {
            return termstring.get(new AbbrevWrapper(t));
        }

        /**
         * Returns the term which is mapped to the abbreviation s, null if no
         * term is mapped to the abbreviation.
         */
        public Term getTerm(String s) {
            return stringterm.get(s).getTerm();
        }

        /**
         * Returns true if the mapping is enabled, which means that the
         * abbreviation may be used.
         */
        public boolean isEnabled(Term t) {
            Boolean b = termenabled.get(new AbbrevWrapper(t));
            if (b != null)
                return b.booleanValue();
            return false;
        }

        /**
         * Associates a Term and its abbreviation in this map.
         * 
         * @param t
         *                a term
         * @param abbreviation
         *                the abbreviation for of this term
         * @param enabled
         *                true if the abbreviation should be used (e.g. when
         *                printing the term), false otherwise.
         */
        public void put(Term t, String abbreviation, boolean enabled)
                throws AbbrevException {
            AbbrevWrapper scw;
            if (containsTerm(t)) {
                throw new AbbrevException("A abbreviation for " + t
                        + " already exists", true);
            }
            // if(containsAbbreviation(abbreviation)){
            // throw new AbbrevException("The abbreviation "+abbreviation+" is
            // already"+
            // " in use for: "+getTerm(abbreviation),false);
            // }
            scw = new AbbrevWrapper(t);
            termstring.put(scw, abbreviation);
            stringterm.put(abbreviation, scw);
            termenabled.put(scw, enabled ? Boolean.TRUE : Boolean.FALSE);
        }

        /**
         * Sets the mapping of the term t to its abbreviation enabled or
         * disabled
         * 
         * @param t
         *                a Term
         * @param enabled
         *                true if the abbreviation of t may be used.
         */
        public void setEnabled(Term t, boolean enabled) {
            termenabled.put(new AbbrevWrapper(t), enabled ? Boolean.TRUE : Boolean.FALSE);
        }

    }

    class AbbrevWrapper {

        private Term t;

        public AbbrevWrapper(Term t) {
            this.t = t;
        }

        public boolean equals(Object o) {
            if (!(o instanceof AbbrevWrapper))
                return false;
            AbbrevWrapper scw = (AbbrevWrapper) o;
            if (scw.getTerm() == t)
                return true;
            return t.equals(scw.getTerm());
        }

        public Term getTerm() {
            return t;
        }

        public int hashCode() {
            return t.hashCode();
        }

    }

}
