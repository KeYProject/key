package de.uka.ilkd.key.macros;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.SortCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public abstract class AbstractBlastingMacro extends StrategyProofMacro {

    protected abstract RuleFilter getSemanticsRuleFilter();
    protected abstract RuleFilter getEqualityRuleFilter();
    protected abstract Set<String> getAllowedPullOut();
    

    @Override
    protected Strategy createStrategy(KeYMediator mediator,
            PosInOccurrence posInOcc) {

        
        Sort nullSort = mediator.getServices().getTypeConverter().getHeapLDT().getNull().sort();
        Goal goal = mediator.getSelectedGoal();

        SortCollector sortCollector = new SortCollector();

        for(SequentFormula sf : goal.sequent()){
            sf.formula().execPreOrder(sortCollector);
        }

        Set<Sort> sorts = sortCollector.getSorts();
        sorts.remove(nullSort);
        List<SequentFormula> formulae =  createFormulae(mediator,sorts);
        for(SequentFormula sf : formulae){
            Sequent s = goal.sequent();
            Semisequent antecedent = s.antecedent();
            if(!antecedent.containsEqual(sf)){
                goal.addFormula(sf, true, true);
            }
        }
        return new SemanticsBlastingStrategy();
    }

    private boolean containsSubTypes(Sort s, Set<Sort> sorts){      
        for(Sort st : sorts){
            if( st.extendsTrans(s)){
                return true;
            }
        }
        return false;
    }

    private List<SequentFormula> createFormulae(KeYMediator mediator, Set<Sort> sorts){
        List<SequentFormula> result = new LinkedList<SequentFormula>();

        Services services = mediator.getServices();
        JavaInfo info = mediator.getJavaInfo();
        TermBuilder tb = new TermBuilder(services.getTermFactory(), services);
        SpecificationRepository spec = services.getSpecificationRepository();

        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();

        LogicVariable h = new LogicVariable(new Name("h"), heapSort);



        for(KeYJavaType kjt : info.getAllKeYJavaTypes()){

            Sort sort = kjt.getSort();

            if(!containsSubTypes(sort, sorts)){
                continue;
            }

            if(!(kjt.getJavaType() instanceof ClassDeclaration 
                    || kjt.getJavaType() instanceof InterfaceDeclaration || kjt.getJavaType() instanceof ArrayDeclaration) 
                    )  {
                continue;
            }
            
            //System.err.println("Sort: "+sort);



            LogicVariable o = new LogicVariable(new Name("o"), kjt.getSort());
            Term exactInstance = tb.exactInstance(kjt.getSort(), tb.var(o));
            for(ClassAxiom c : spec.getClassAxioms(kjt)){

                if(c instanceof RepresentsAxiom && c.getKJT().equals(kjt)){
                    RepresentsAxiom ra = (RepresentsAxiom) c;

                    try{

                        Term t = ra.getAxiom(h, o, services);
                        //System.err.println(c.getName());
                        if(t.op().equals(Equality.EQV)){

                            Term left = t.sub(0);
                            Term right = t.sub(1);

                            Term equivalence = t;
                            Term implication;

                            Term[] heaps = new Term[1];
                            heaps[0] = tb.var(h);

                            Term inv = tb.inv(heaps, tb.var(o));

                            if(left.op().name().equals(inv.op().name())){

                                implication = tb.imp(left, right);

                                Term exactInstanceEquiv = tb.imp(exactInstance, equivalence);
                                Term instanceImpl = implication;

                                exactInstanceEquiv = tb.all(h, tb.all(o, exactInstanceEquiv));
                                instanceImpl = tb.all(h, tb.all(o, instanceImpl));
                                
                                result.add(new SequentFormula(exactInstanceEquiv));

                                if(!right.equals(tb.tt())){
                                    result.add(new SequentFormula(instanceImpl));
                                }
                            }
                            else if(right.op().name().equals(inv.op().name())){

                                Term exactInstanceEquiv = tb.imp(exactInstance, equivalence);
                                implication = tb.imp(right, left);
                                Term instanceImpl = implication;

                                exactInstanceEquiv = tb.all(h, tb.all(o, exactInstanceEquiv));
                                instanceImpl = tb.all(h, tb.all(o, instanceImpl));

                                result.add(new SequentFormula(exactInstanceEquiv));

                                if(!left.equals(tb.tt())){
                                    result.add(new SequentFormula(instanceImpl));
                                }

                            }
                            else{
                                Term f = t;
                                f = tb.all(h, tb.all(o, f));                            
                                result.add(new SequentFormula(f));
                            }
                        }
                        else{
                            Term f = t;
                            f = tb.all(h, tb.all(o, f));                            
                            result.add(new SequentFormula(f));
                        }
                        
                    }catch(Exception e){

                        //System.err.println(e.getMessage());

                    }

                }
            }
        }
        return result;
    }




    private class SemanticsBlastingStrategy implements Strategy{

        @Override
        public Name name() {
            return new Name("Semantics Blasting");
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio,
                Goal goal) {

            if(app.rule() instanceof OneStepSimplifier){
                return NumberRuleAppCost.getZeroCost();
            }
            //          else if(app.rule().name().toString().equals("applyEq")){
            //              return LongRuleAppCost.ZERO_COST;
            //          }
            else if(getSemanticsRuleFilter().filter(app.rule())){
                return NumberRuleAppCost.create(1);
            }           
            else if(getEqualityRuleFilter().filter(app.rule())){
                return NumberRuleAppCost.create(10);
            }
            else if(app.rule().name().toString().equals("pullOut")){
                Term t = pio.subTerm();

                //System.out.println(t);

                if(t.op() instanceof Function){
                    if(getAllowedPullOut().contains(t.op().name().toString())){
                        return NumberRuleAppCost.create(1000);
                    }
                }

            }



            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

            if(app.rule() instanceof OneStepSimplifier){
                return true;
            }


            Rule rule = app.rule();

            String name = rule.name().toString();

            //System.out.println(rule.name());

            return name.equals("pullOut") 
                    //||name.startsWith("applyEq")
                    || getSemanticsRuleFilter().filter(rule) 
                    || getEqualityRuleFilter().filter(rule);

        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {}

    }

}