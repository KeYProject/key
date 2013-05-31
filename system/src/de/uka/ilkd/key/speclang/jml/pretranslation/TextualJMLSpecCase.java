// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML specification case (i.e., more or less an operation contract) in 
 * textual form. Is also used for block contracts.
 */
public final class TextualJMLSpecCase extends TextualJMLConstruct {
   
    private final Behavior behavior;
    private PositionedString workingSpace = null;
    private ImmutableList<PositionedString> measuredBy =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> accessible =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signals =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signalsOnly =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> diverges =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> depends =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> breaks =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> continues =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> returns =
            ImmutableSLList.<PositionedString>nil();

    private Map<String, ImmutableList<PositionedString>>
      assignables = new LinkedHashMap<String, ImmutableList<PositionedString>>();

    private Map<String, ImmutableList<PositionedString>>
      requires = new LinkedHashMap<String, ImmutableList<PositionedString>>();

    private Map<String, ImmutableList<PositionedString>>
      ensures = new LinkedHashMap<String, ImmutableList<PositionedString>>();

    public TextualJMLSpecCase(ImmutableList<String> mods,
                              Behavior behavior) {
        super(mods);
        assert behavior != null;
        this.behavior = behavior;
        for(Name hName : HeapLDT.VALID_HEAP_NAMES) {
          assignables.put(hName.toString(), ImmutableSLList.<PositionedString>nil());
          requires.put(hName.toString(), ImmutableSLList.<PositionedString>nil());
          ensures.put(hName.toString(), ImmutableSLList.<PositionedString>nil());
        }
    }
    
    static TextualJMLSpecCase assert2blockContract (ImmutableList<String> mods, PositionedString assertStm) {
        final TextualJMLSpecCase res = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
        res.addName(new PositionedString("assert "+assertStm.text, assertStm.fileName, assertStm.pos));
        res.addRequires(assertStm);
        res.addEnsures(assertStm);
        res.addAssignable(new PositionedString("assignable \\strictly_nothing;",assertStm.fileName,assertStm.pos));
        return res;
    }


    public void addName(PositionedString n) {
        this.name = n.text;
    }

    public void addRequires(PositionedString ps) {
        addGeneric(requires, ps);
    }


    public void addRequires(ImmutableList<PositionedString> l) {
        for(PositionedString ps : l) {
           addRequires(ps);
        }
    }

    public void addMeasuredBy(PositionedString ps) {
        measuredBy = measuredBy.append(ps);
    }


    public void addMeasuredBy(ImmutableList<PositionedString> l) {
        measuredBy = measuredBy.append(l);
    }


    public void addAssignable(PositionedString ps) {
        addGeneric(assignables, ps);
    }

    public void addAccessible(PositionedString ps) {
        accessible = accessible.append(ps);
    }


    public void addAccessible(ImmutableList<PositionedString> l) {
        accessible = accessible.append(l);
    }


    public void addEnsures(PositionedString ps) {
        addGeneric(ensures, ps);
    }


    public void addEnsures(ImmutableList<PositionedString> l) {
        for(PositionedString ps : l) {
           addEnsures(ps);
        }
    }


    public void addSignals(PositionedString ps) {
        signals = signals.append(ps);
    }


    public void addSignals(ImmutableList<PositionedString> l) {
        signals = signals.append(l);
    }


    public void addSignalsOnly(PositionedString ps) {
        signalsOnly = signalsOnly.append(ps);
    }


    public void addSignalsOnly(ImmutableList<PositionedString> l) {
        signalsOnly = signalsOnly.append(l);
    }


    public void setWorkingSpace(PositionedString ps) {
        workingSpace = ps;
    }


    public void addDiverges(PositionedString ps) {
        diverges = diverges.append(ps);
    }


    public void addDepends(PositionedString ps) {
        depends = depends.append(ps);
    }

    
    public void addBreaks(PositionedString ps) {
        breaks = breaks.append(ps);
    }


    public void addBreaks(ImmutableList<PositionedString> l) {
        breaks = breaks.append(l);
    }


    public void addContinues(PositionedString ps) {
        continues = continues.append(ps);
    }


    public void addContinues(ImmutableList<PositionedString> l) {
        continues = continues.append(l);
    }


    public void addReturns(PositionedString ps) {
        returns = returns.append(ps);
    }


    public void addReturns(ImmutableList<PositionedString> l) {
        returns = returns.append(l);
    }


    public Behavior getBehavior() {
        return behavior;
    }


    public ImmutableList<PositionedString> getRequires() {
        return requires.get(HeapLDT.BASE_HEAP_NAME.toString());
    }

    public ImmutableList<PositionedString> getRequires(String hName) {
        return requires.get(hName);
    }

    public ImmutableList<PositionedString> getMeasuredBy() {
        return measuredBy;
    }


    public ImmutableList<PositionedString> getAssignable() {
        return assignables.get(HeapLDT.BASE_HEAP_NAME.toString());
    }

    public ImmutableList<PositionedString> getAssignable(String hName) {
        return assignables.get(hName);
    }

    public ImmutableList<PositionedString> getAccessible() {
        return accessible;
    }


    public ImmutableList<PositionedString> getEnsures() {
        return ensures.get(HeapLDT.BASE_HEAP_NAME.toString());
    }

    public ImmutableList<PositionedString> getEnsures(String hName) {
        return ensures.get(hName);
    }


    public String getName() {
        return name;
    }


    public ImmutableList<PositionedString> getSignals() {
        return signals;
    }


    public ImmutableList<PositionedString> getSignalsOnly() {
        return signalsOnly;
    }


    public PositionedString getWorkingSpace() {
        return workingSpace;
    }


    public ImmutableList<PositionedString> getDiverges() {
        return diverges;
    }


    public ImmutableList<PositionedString> getDepends() {
        return depends;
    }


    public ImmutableList<PositionedString> getBreaks() {
        return breaks;
    }


    public ImmutableList<PositionedString> getContinues() {
        return continues;
    }


    public ImmutableList<PositionedString> getReturns() {
        return returns;
    }


    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;

        sb.append(behavior).append("\n");
        for(Name h : HeapLDT.VALID_HEAP_NAMES) {
          it = requires.get(h.toString()).iterator();
          while(it.hasNext()) {
            sb.append("requires<"+h+">: " + it.next() + "\n");
          }
        }
        for(Name h : HeapLDT.VALID_HEAP_NAMES) {
          it = assignables.get(h.toString()).iterator();
          while(it.hasNext()) {
            sb.append("assignable<"+h+">: " + it.next() + "\n");
          }
        }
        it = accessible.iterator();
        while (it.hasNext()) {
            sb.append("accessible: " + it.next() + "\n");
        }
        for(Name h : HeapLDT.VALID_HEAP_NAMES) {
          it = ensures.get(h.toString()).iterator();
          while(it.hasNext()) {
            sb.append("ensures<"+h+">: " + it.next() + "\n");
          }
        }
        it = signals.iterator();
        while (it.hasNext()) {
            sb.append("signals: ").append(it.next()).append("\n");
        }
        it = signalsOnly.iterator();
        while (it.hasNext()) {
            sb.append("signals_only: ").append(it.next()).append("\n");
        }
        it = diverges.iterator();
        while (it.hasNext()) {
            sb.append("diverges: ").append(it.next()).append("\n");
        }
        it = depends.iterator();
        while (it.hasNext()) {
            sb.append("depends: ").append(it.next()).append("\n");
        }
        it = breaks.iterator();
        while (it.hasNext()) {
            sb.append("breaks: ").append(it.next()).append("\n");
        }
        it = continues.iterator();
        while (it.hasNext()) {
            sb.append("continues: ").append(it.next()).append("\n");
        }
        it = returns.iterator();
        while (it.hasNext()) {
            sb.append("returns: ").append(it.next()).append("\n");
        }
        return sb.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLSpecCase)) {
            return false;
        }
        TextualJMLSpecCase sc = (TextualJMLSpecCase) o;
        return mods.equals(sc.mods)
               && behavior.equals(sc.behavior)
               && requires.equals(sc.requires)
               && assignables.equals(sc.assignables)
               && accessible.equals(sc.accessible)
               && ensures.equals(sc.ensures)
               && signals.equals(sc.signals)
               && signalsOnly.equals(sc.signalsOnly)
               && diverges.equals(sc.diverges)
               && depends.equals(sc.depends)
               && breaks.equals(sc.breaks)
               && continues.equals(sc.continues)
               && returns.equals(sc.returns);
    }


    @Override
    public int hashCode() {
        return mods.hashCode()
               + behavior.hashCode()
               + requires.hashCode()
               + assignables.hashCode()
               + accessible.hashCode()
               + ensures.hashCode()
               + signals.hashCode()
               + signalsOnly.hashCode()
               + diverges.hashCode()
               + depends.hashCode()
               + breaks.hashCode()
               + continues.hashCode()
               + returns.hashCode();
    }
}
