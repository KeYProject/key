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

package de.uka.ilkd.key.rule.conditions;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestDropEffectlessElementary extends TestCase {

    public void testSelfAssignments() throws Exception {

        Term term = TacletForTests.parseTerm("{ i := i }(i=0)");
        Term result = applyDrop(term);
        assertEquals(term, result);

        term = TacletForTests.parseTerm("{ i := i || i := 0 }(i=0)");
        result = applyDrop(term);
        Term expected = TacletForTests.parseTerm("{i:=0}(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ i := 0 || i := i }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("{i:=i}(i=0)");
        assertEquals(expected, result);
    }

    public void testDoubleAssignment() throws Exception {

        Term term = TacletForTests.parseTerm("{ i := j || j := i }(i=0)");
        Term result = applyDrop(term);
        Term expected = TacletForTests.parseTerm("{i := j}(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ j := 5 || j := j }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("(i=0)");
        assertEquals(expected, result);

        term = TacletForTests.parseTerm("{ i:=i || j := 5 || i:=i || j := j }(i=0)");
        result = applyDrop(term);
        expected = TacletForTests.parseTerm("{i:=i}(i=0)");
        assertEquals(expected, result);
    }

    // this was bug #1269
    public void testFaultyCase() throws Exception {
        // The parser cannot parse this but this can appear as 
        // result of the sequential to parallel of {i:=i+1}{i:=i}

        Term term;
        // Term term = TacletForTests.parseTerm("{ {i := i+1}i:=i }(i=0)");
        {
            TermBuilder df = TermBuilder.DF;
            Term t0 = TacletForTests.parseTerm("{i := i+1}0").sub(0);
            Term t1 = TacletForTests.parseTerm("{i := i}0").sub(0);
            Term t2 = TacletForTests.parseTerm("i=0");
            Term t3 = df.apply(t0, t1, null);
            term = df.apply(t3, t2, null);
        }
        assertEquals("{{i:=i + 1}i:=i}(i = 0)", 
                LogicPrinter.quickPrintTerm(term, TacletForTests.services).trim());

        Term result = applyDrop(term);
        assertEquals(term, result);
    }

    //    the following cannot be parsed apparently.
    //    public void testUpdatedUpdate() throws Exception {
    //        Term term = TacletForTests.parseTerm("({i:=i}{i := i})(i=0)");
    //        Term result = applyDrop(term);
    //        Term expected = TacletForTests.parseTerm("i=0");
    //        assertEquals(expected, result);
    //        
    //        term = TacletForTests.parseTerm("({i:=i}{j:=5})(i=0)");
    //        result = applyDrop(term);
    //        expected = TacletForTests.parseTerm("(i=0)");
    //        assertEquals(expected, result);
    //    }

    private Term applyDrop(Term term) {

        Term update = term.sub(0);
        Term arg = term.sub(1);

        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable x = SchemaVariableFactory.createFormulaSV(new Name("x"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));
        DropEffectlessElementariesCondition cond = new DropEffectlessElementariesCondition(u,x,result);

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(u, update, TacletForTests.services());
        svInst = svInst.add(x, arg, TacletForTests.services());

        MatchConditions mc = MatchConditions.EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        // first 2 args are not used in the following method, hence, can be null.
        mc = cond.check(null, null, mc, TacletForTests.services());

        if(mc == null) {
            return term; 
        }

        return mc.getInstantiations().getTermInstantiation(result, null, TacletForTests.services());
    }

}
