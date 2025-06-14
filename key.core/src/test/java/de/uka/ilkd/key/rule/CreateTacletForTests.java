/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.parser.AbstractTestTermParser;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * create Taclet for test cases.
 */
public class CreateTacletForTests extends AbstractTestTermParser {
    private static final Logger LOGGER = LoggerFactory.getLogger(CreateTacletForTests.class);
    private Sort nat;

    public static AntecTaclet impleft;
    public static SuccTaclet impright;
    public static SuccTaclet imprightadd;
    public static AntecTaclet notleft;
    public static SuccTaclet notright;
    public static SuccTaclet close;
    public static SuccTaclet allright;
    public static AntecTaclet allleft;
    public static RewriteTaclet contradiction;
    public static NoFindTaclet cut;
    public static RewriteTaclet predsuccelim;
    public static RewriteTaclet pluszeroelim;
    public static RewriteTaclet zeropluselim;
    public static RewriteTaclet succelim;
    public static RewriteTaclet switchsecondsucc;
    public static RewriteTaclet switchfirstsucc;
    public static SuccTaclet closewitheq;

    static Function func_0;
    static Function func_eq;
    static Function func_plus;
    static Function func_min1;
    static Function func_plus1;
    static Function func_p; // Sort.FORMULA

    static Sequent seq_test1;
    static Sequent seq_test2;
    static Sequent seq_test3;
    public static Sequent seq_testNat;
    static Sequent seq_testAll;

    static SchemaVariable b;
    static LogicVariable z;
    static Sort sort1;
    static TermFactory tf;

    static NamespaceSet nss;

    public final Services services;

    public CreateTacletForTests() {
        services = new Services(AbstractProfile.getDefaultProfile());
        tf = services.getTermFactory();
    }


    public void createTaclets() {
        impleft = (AntecTaclet) parseTaclet(
            "imp_left{\\find(b->b0==>) \\replacewith(b0==>); \\replacewith(==> b)}");
        impright = (SuccTaclet) parseTaclet("imp_right{\\find(==> b->b0) \\replacewith(b ==> b0)}");
        notleft = (AntecTaclet) parseTaclet("not_left{\\find(not b==>) \\replacewith(==>b)}");
        notright = (SuccTaclet) parseTaclet("not_right{\\find(==>not b) \\replacewith(b==>)}");
        cut = (NoFindTaclet) parseTaclet("cut{\\add(b==>); \\add(==>b)}");
        imprightadd = (SuccTaclet) parseTaclet(
            "imp_right_add{\\find(==> b->b0) \\replacewith(b==>b0) \\addrules("
                + "cut{\\add(b==>); \\add(==>b)})}");
        close = (SuccTaclet) parseTaclet("close_goal{\\assumes (b==>) \\find(==>b) \\closegoal}");
        contradiction =
            (RewriteTaclet) parseTaclet("contracdiction{\\find(b->b0) \\replacewith(!b0 -> !b)}");
        allright = (SuccTaclet) parseTaclet(
            "all_right{\\find (==> \\forall z; b) \\varcond ( \\newDependingOn(x, b) ) \\replacewith (==> {\\subst z; x}b)}");
        allleft = (AntecTaclet) parseTaclet(
            "all_left{\\find(\\forall z; b==>) \\add({\\subst z; x}b==>)}");

    }

    private Taclet parseTaclet(String tacletString) {
        return io.load(tacletString).loadTaclets().get(0);
    }


    public void createNatTaclets() {
        // decls for nat
        func_0 = new JFunction(new Name("zero"), nat, new Sort[] {});
        func_eq = new JFunction(new Name("="), JavaDLTheory.FORMULA, nat, nat);
        func_plus = new JFunction(new Name("+"), nat, nat, nat);
        func_min1 = new JFunction(new Name("pred"), nat, nat);
        func_plus1 = new JFunction(new Name("succ"), nat, nat);

        nss.functions().add(func_0);
        nss.functions().add(func_eq);
        nss.functions().add(func_plus);
        nss.functions().add(func_min1);
        nss.functions().add(func_plus1);

        TermSV var_rn = SchemaVariableFactory.createTermSV(new Name("rn"), nat);
        TermSV var_rm = SchemaVariableFactory.createTermSV(new Name("rm"), nat);

        JTerm t_rn = tf.createTerm(var_rn);
        JTerm t_rm = tf.createTerm(var_rm);
        JTerm t_0 = tf.createTerm(func_0);
        JTerm t_rnminus1 = tf.createTerm(func_min1, t_rn);
        JTerm t_rnminus1plus1 = tf.createTerm(func_plus1, t_rnminus1);
        JTerm t_rneq0 = tf.createTerm(func_eq, t_rn, t_0);
        // Term t_0minus1=tf.createTerm(func_min1,
        // new Term[]{t_0});
        JTerm t_0plus1 = tf.createTerm(func_plus1, t_0);

        // help rule r1: find(rn) replacewith(0) replacewith(0)
        RewriteTacletBuilder<RewriteTaclet> rwb1 = new RewriteTacletBuilder<>();
        rwb1.setName(new Name("r1"));
        rwb1.setFind(t_rn);
        rwb1.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t_0));



        // pred-succ-elim-rule
        // find(rn -1 +1) replacewith(rn) replacewith(0 +1) addrule(r1)
        RewriteTacletBuilder<RewriteTaclet> rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(t_rnminus1plus1);
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t_rn));
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.<Taclet>nil().prepend(rwb1.getTaclet()), t_0plus1));
        rwbuilder.setName(new Name("pred-succ-elim"));
        pluszeroelim = rwbuilder.getRewriteTaclet();

        // plus-zero-elim
        // find(rn + 0) replacewith(rn)
        rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(tf.createTerm(func_plus, t_rn, t_0));
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t_rn));
        rwbuilder.setName(new Name("plus-zero-elim"));
        predsuccelim = rwbuilder.getRewriteTaclet();

        // zero-plus-elim
        // find(0 + rn) replacewith(rn)
        rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(tf.createTerm(func_plus, t_0, t_rn));
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t_rn));
        rwbuilder.setName(new Name("zero-plus-elim"));
        zeropluselim = rwbuilder.getRewriteTaclet();


        // closewitheq
        // find(=> rn=rn)
        SuccTacletBuilder sbuilder = new SuccTacletBuilder();
        JTerm t_rneqrn = tf.createTerm(func_eq, t_rn, t_rn);
        sbuilder.setFind(t_rneqrn);
        sbuilder.setName(new Name("close-with-eq"));
        closewitheq = sbuilder.getSuccTaclet();


        // switch first succ
        // find((rn +1) + rm) replacewith((rn + rm) +1)
        JTerm t_rnplus1 = tf.createTerm(func_plus1, t_rn);
        JTerm t_rnplus1plusrm = tf.createTerm(func_plus, t_rnplus1, t_rm);

        JTerm t_rnplusrm = tf.createTerm(func_plus, t_rn, t_rm);
        JTerm t_rnplusrmplus1 = tf.createTerm(func_plus1, t_rnplusrm);

        rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(t_rnplus1plusrm);
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(), t_rnplusrmplus1));
        rwbuilder.setName(new Name("switch-first-succ"));
        switchfirstsucc = rwbuilder.getRewriteTaclet();



        // switch second succ
        // find(rn + (rm +1)) replacewith((rn + rm) +1)
        JTerm t_rmplus1 = tf.createTerm(func_plus1, t_rm);
        JTerm t_rnplus_rmplus1 = tf.createTerm(func_plus, t_rn, t_rmplus1);
        rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(t_rnplus_rmplus1);
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(), t_rnplusrmplus1));
        rwbuilder.setName(new Name("switch-second-succ"));
        switchsecondsucc = rwbuilder.getRewriteTaclet();

        // elim-succ
        // find(rn +1 = rm +1) replacewith(rn=rm)
        JTerm t_rneqrm = tf.createTerm(func_eq, t_rn, t_rm);
        rwbuilder = new RewriteTacletBuilder<>();
        rwbuilder.setFind(tf.createTerm(func_eq, t_rnplus1, t_rmplus1));
        rwbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t_rneqrm));
        rwbuilder.setName(new Name("succ-elim"));
        succelim = rwbuilder.getRewriteTaclet();

    }

    public void setUp() throws IOException {
        nss = new NamespaceSet();

        parseDecls("""
                \\sorts { Nat; testSort1; }
                \\schemaVariables {
                  \\formula b,b0;
                  \\term testSort1 x;
                  \\variables testSort1 z;
                }
                """);

        sort1 = nss.sorts().lookup(new Name("testSort1"));
        nat = nss.sorts().lookup(new Name("Nat"));

        b = (SchemaVariable) nss.variables().lookup(new Name("b"));

        // createTaclets
        createTaclets();
        createNatTaclets();

        // problem

        String test1 = "\\predicates {A; B; } (A -> B) -> (!(!(A -> B)))";
        JTerm t_test1 = null;
        try {
            t_test1 =
                (JTerm) io.load(test1).loadDeclarations().loadProblem().getProblem().succedent()
                        .get(0).formula();
        } catch (Exception e) {
            LOGGER.error("Parser Error or Input Error", e);
            fail("Parser Error");
        }
        SequentFormula cf = new SequentFormula(t_test1);
        SequentFormula cf2 = new SequentFormula(t_test1);
        seq_test1 =
            JavaDLSequentKit.createSequent(ImmutableSLList.nil(), ImmutableSLList.singleton(cf));
        seq_test2 =
            JavaDLSequentKit.createSequent(ImmutableSLList.singleton(cf), ImmutableSLList.nil());
        seq_test3 = JavaDLSequentKit.createSequent(ImmutableSLList.singleton(cf),
            ImmutableSLList.singleton(cf2));


        func_p = new JFunction(new Name("P"), JavaDLTheory.FORMULA, sort1);
        nss.functions().add(func_p);

        // nat problem:
        Function const_c = new JFunction(new Name("c"), nat, new SortImpl[0]);
        nss.functions().add(const_c);
        Function const_d = new JFunction(new Name("d"), nat, new SortImpl[0]);
        nss.functions().add(const_d);

        JTerm t_c = tf.createTerm(const_c);
        JTerm t_d = tf.createTerm(const_d);
        JTerm t_cplusd = tf.createTerm(func_plus, t_c, t_d);
        JTerm t_dminus1 = tf.createTerm(func_min1, t_d);
        JTerm t_dminus1plus1 = tf.createTerm(func_plus1, t_dminus1);
        JTerm t_dminus1plus1plusc = tf.createTerm(func_plus, t_dminus1plus1, t_c);
        JTerm t_eq1 = tf.createTerm(func_eq, t_cplusd, t_dminus1plus1plusc);


        JTerm t_cplus1 = tf.createTerm(func_plus1, t_c);
        JTerm t_cplus1plusd = tf.createTerm(func_plus, t_cplus1, t_d);
        JTerm t_dpluscplus1 = tf.createTerm(func_plus, t_d, t_cplus1);
        JTerm t_eq2 = tf.createTerm(func_eq, t_cplus1plusd, t_dpluscplus1);
        JTerm tnat = tf.createTerm(Junctor.IMP, t_eq1, t_eq2);

        // => (c+d) = ((d -1 +1) +c) -> (c +1)+d = (d+c) +1
        seq_testNat = JavaDLSequentKit.createSequent(ImmutableSLList.nil(),
            ImmutableSLList.singleton(new SequentFormula(tnat)));


        z = new LogicVariable(new Name("z"), sort1);
        JTerm t_z = tf.createTerm(z);
        JTerm t_allzpz = services.getTermBuilder().all(z, tf.createTerm(func_p, t_z));
        SequentFormula cf3 = new SequentFormula(t_allzpz);
        seq_testAll = JavaDLSequentKit.createSequent(ImmutableSLList.nil(),
            ImmutableSLList.singleton(cf3));



    }
}
