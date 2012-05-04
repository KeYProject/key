// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML specification case (i.e., more or less an operation contract) in 
 * textual form.
 */
public final class TextualJMLSpecCase extends TextualJMLConstruct {
   
    static final List<String> validHeaps = new ArrayList<String>();

    static {
      validHeaps.add("heap");
      validHeaps.add("savedHeap");
      // validHeaps.add("permissions");
    }; 

    private final Behavior behavior;
    private PositionedString workingSpace = null;
    private ImmutableList<PositionedString> requires =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> measuredBy =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> accessible =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> ensures =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signals =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signalsOnly =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> diverges =
            ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> depends =
            ImmutableSLList.<PositionedString>nil();

    private Map<String, ImmutableList<PositionedString>>
      assignables = new HashMap<String, ImmutableList<PositionedString>>();

    public TextualJMLSpecCase(ImmutableList<String> mods,
                              Behavior behavior) {
        super(mods);
        assert behavior != null;
        this.behavior = behavior;
        for(String hName : validHeaps) {
          assignables.put(hName, ImmutableSLList.<PositionedString>nil());
        }
    }


    public void addName(PositionedString n) {
        this.name = n.text;
    }


    public void addRequires(PositionedString ps) {
        requires = requires.append(ps);
    }


    public void addRequires(ImmutableList<PositionedString> l) {
        requires = requires.append(l);
    }


    public void addMeasuredBy(PositionedString ps) {
        measuredBy = measuredBy.append(ps);
    }


    public void addMeasuredBy(ImmutableList<PositionedString> l) {
        measuredBy = measuredBy.append(l);
    }


    public void addAssignable(PositionedString ps) {
        String t = ps.text;
        if(!t.startsWith("<")) {
           ImmutableList<PositionedString> l = assignables.get("heap");
           l = l.append(ps);
           assignables.put("heap", l);
           return; 
        }
        List<String> hs = new ArrayList<String>();
        for(String hName : validHeaps) {
          String h = "<" + hName + ">";
          if(t.startsWith(h)) {
            hs.add(hName);
            t = t.substring(h.length());
          }
        }
        ps = new PositionedString(t, ps.fileName, ps.pos);
        for(String h : hs) {
           ImmutableList<PositionedString> l = assignables.get(h);
           l = l.append(ps);
           assignables.put(h, l); 
        }
    }

//    public void addAssignableBackup(PositionedString ps) {
        //assignable_backup = assignable_backup.append(ps);
//    }


//    public void addAssignableBackup(ImmutableList<PositionedString> l) {
        //assignable_backup = assignable_backup.append(l);
//    }


    public void addAccessible(PositionedString ps) {
        accessible = accessible.append(ps);
    }


    public void addAccessible(ImmutableList<PositionedString> l) {
        accessible = accessible.append(l);
    }


    public void addEnsures(PositionedString ps) {
        ensures = ensures.append(ps);
    }


    public void addEnsures(ImmutableList<PositionedString> l) {
        ensures = ensures.append(l);
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


    public Behavior getBehavior() {
        return behavior;
    }


    public ImmutableList<PositionedString> getRequires() {
        return requires;
    }


    public ImmutableList<PositionedString> getMeasuredBy() {
        return measuredBy;
    }


    public ImmutableList<PositionedString> getAssignable() {
        return assignables.get("heap");
    }

    public ImmutableList<PositionedString> getAssignable(String hName) {
        return assignables.get(hName);
    }

    public ImmutableList<PositionedString> getAssignableBackup() {
        return assignables.get("savedHeap");
    }

    public ImmutableList<PositionedString> getAccessible() {
        return accessible;
    }


    public ImmutableList<PositionedString> getEnsures() {
        return ensures;
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


    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;

        sb.append(behavior).append("\n");
        it = requires.iterator();
        while (it.hasNext()) {
            sb.append("requires: ").append(it.next()).append("\n");
        }
        for(String h : TextualJMLSpecCase.validHeaps) {
          it = assignables.get(h).iterator();
          while(it.hasNext()) {
            sb.append("assignable<"+h+">: " + it.next() + "\n");
          }
        }
        it = accessible.iterator();
        while (it.hasNext()) {
            sb.append("accessible: " + it.next() + "\n");
        }
        it = ensures.iterator();
        while (it.hasNext()) {
            sb.append("ensures: ").append(it.next()).append("\n");
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
               && depends.equals(sc.depends);
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
               + depends.hashCode();
    }
}
