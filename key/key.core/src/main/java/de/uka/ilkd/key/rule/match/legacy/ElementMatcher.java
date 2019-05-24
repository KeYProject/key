package de.uka.ilkd.key.rule.match.legacy;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.AbstractSV;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.rule.inst.TermLabelInstantiationEntry;
import de.uka.ilkd.key.util.Debug;


public abstract class ElementMatcher<T extends Operator> {

    @SuppressWarnings("unchecked")
    static <T extends Operator> ElementMatcher<? super T> getElementMatcherFor(T o) {
        if (o instanceof SchemaVariable) {
            if (o instanceof TermSV) {
                return (ElementMatcher<? super T>) termSVMatcher;
            } else if (o instanceof FormulaSV) {
                return (ElementMatcher<? super T>) formulaSVMatcher;
            } else if (o instanceof ProgramSV) {
                return (ElementMatcher<? super T>) programSVMatcher;
            } else if (o instanceof UpdateSV) {
                return (ElementMatcher<? super T>) updateSVMatcher;
            } else if (o instanceof ModalOperatorSV) {
                return (ElementMatcher<? super T>) modalSVMatcher;
            } else if (o instanceof VariableSV) {
                return (ElementMatcher<? super T>) variableSVMatcher;
            } else if (o instanceof SkolemTermSV) {
                return (ElementMatcher<? super T>) skolemSVMatcher;
            } else if (o instanceof TermLabelSV) {
                return (ElementMatcher<? super T>) termLabelSVMatcher;
            }            
        } else if (o instanceof ElementaryUpdate) {
            return (ElementMatcher<? super T>) elUpMatcher;
        } else if (o instanceof SortDependingFunction) {
            return (ElementMatcher<? super T>) sortDependingFctMatcher;
        } else if (o instanceof LogicVariable) {
            return (ElementMatcher<? super T>) logicVarMatcher;
        }
        return IDENTITY_MATCHER;
    }

    private final static IdentityOperatorMatcher IDENTITY_MATCHER = new IdentityOperatorMatcher();
    private final static ElementaryUpdateMatcher elUpMatcher = new ElementaryUpdateMatcher();
    private final static SortDependingFunctionMatcher sortDependingFctMatcher = new SortDependingFunctionMatcher();
    private final static LogicVariableMatcher logicVarMatcher = new LogicVariableMatcher();    
    private final static TermSVMatcher termSVMatcher = new TermSVMatcher();
    private final static FormulaSVMatcher formulaSVMatcher = new FormulaSVMatcher();
    private final static ProgramSVMatcher programSVMatcher = new ProgramSVMatcher();
    private final static ModalOperatorSVMatcher modalSVMatcher = new ModalOperatorSVMatcher();
    private final static UpdateSVMatcher updateSVMatcher = new UpdateSVMatcher();
    private final static SkolemTermSVMatcher skolemSVMatcher = new SkolemTermSVMatcher();
    private final static TermLabelSVMatcher termLabelSVMatcher = new TermLabelSVMatcher();
    private final static VariableSVMatcher variableSVMatcher = new VariableSVMatcher();
    
    
    private static abstract class AbstractSVMatcher<S extends AbstractSV> extends ElementMatcher<S> {

        /**
         * tries to add the pair <tt>(op,pe)</tt> to the match conditions. If
         * possible the resulting match conditions are returned, otherwise
         * <tt>null</tt>. Such an addition can fail, e.g. if already a pair
         * <tt>(op,x)</tt> exists where <tt>x<>pe</tt>
         */
        protected MatchConditions addInstantiation(AbstractSV op, ProgramElement pe,
                MatchConditions matchCond, 
                Services services) {

            final SVInstantiations instantiations = matchCond.getInstantiations();
            final SVSubstitute inMap = (SVSubstitute) instantiations.getInstantiation(op);

            if (inMap == null) {            
                try {
                    return matchCond
                            .setInstantiations(instantiations.add(op, pe, services));
                } catch (IllegalInstantiationException e) {
                    Debug
                    .out("Exception thrown by class Taclet at setInstantiations");
                }
            } else {
                Object peForCompare = pe;
                if (inMap instanceof Term) {
                    try {
                        peForCompare = services.getTypeConverter()
                                .convertToLogicElement(
                                        pe,
                                        matchCond.getInstantiations()
                                        .getExecutionContext());                    
                    } catch (RuntimeException re) {
                        Debug.out("Cannot convert program element to term.", op,
                                pe);
                        return null;
                    }
                } 
                if (inMap.equals(peForCompare)) {
                    return matchCond;
                }
            }
            Debug.out("FAILED. Illegal Instantiation.", op, pe);
            return null;
        }

        /**
         * Tries to add the pair <tt>(op,term)</tt> to the match conditions. If
         * successful the resulting conditions are returned, otherwise null. Failure
         * is possible e.g. if this schemavariable has been already matched to a
         * term <tt>t2</tt> which is not unifiable with the given term.
         */
        protected final MatchConditions addInstantiation(AbstractSV op, Term term,
                MatchConditions matchCond, 
                Services services) {

            if (op.isRigid() && !term.isRigid()) {
                Debug.out("FAILED. Illegal Instantiation");
                return null;
            }      

            final SVInstantiations inst = matchCond.getInstantiations();

            final Term t = inst.getTermInstantiation(op, 
                    inst.getExecutionContext(), 
                    services);
            if(t != null) {
                if(!t.equalsModRenaming(term)) {
                    Debug.out("FAILED. Adding instantiations leads to unsatisfiable"
                            + " constraint.", 
                            op, 
                            term);
                    return null;
                } else {
                    return matchCond;
                }
            }

            try {           
                return matchCond.setInstantiations(inst.add(op, term, services));
            } catch (IllegalInstantiationException e) {
                Debug.out("FAILED. Exception thrown at sorted schema variable", e);
            }

            Debug.out("FAILED. Illegal Instantiation");
            return null;
        }
    }
    
    private static class ElementaryUpdateMatcher extends ElementMatcher<ElementaryUpdate> {

        @Override
        public MatchConditions match(ElementaryUpdate op, 
                SVSubstitute subst, 
                MatchConditions mc, Services services) {
            if(op == subst) {
                return mc;
            } else if(! (subst instanceof ElementaryUpdate)) {
                Debug.out("FAILED. Incompatible operators " 
                        + "(template, operator)", op, subst);
                return null;
            } 

            final ElementaryUpdate eu = (ElementaryUpdate) subst;
            final MatchConditions result = 
                    ElementMatcher.getElementMatcherFor(op.lhs()).match(op.lhs(), eu.lhs(), mc, services);
            if(result == null) {
                Debug.out("FAILED. Lhs mismatch " 
                        + "(template, operator)", op, eu);
            }
            return result;
        }
    }
    
    private static class FormulaSVMatcher extends AbstractSVMatcher<FormulaSV> {

        @Override
        public MatchConditions match(FormulaSV op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {
            if (subst instanceof Term) {
                return addInstantiation(op, (Term) subst, mc, services);
            }
            Debug.out("FAILED. Schemavariable of this kind only match terms.");
            return null;
        }

    }
    
    private static class IdentityOperatorMatcher extends ElementMatcher<Operator> {

        /** 
         * implements the default operator matching rule which means 
         * that the compared object have to be equal otherwise
         * matching fails
         */
        @Override
        public MatchConditions match(Operator op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {
            if(subst == op) {
                return mc;
            }
            Debug.out("FAILED. Operators are different(template, candidate)", op, subst);
            return null;
        }

    }
    
    private static class LogicVariableMatcher extends ElementMatcher<LogicVariable> {
        /** 
         * a match between two logic variables is possible if they have been assigned
         * they are same or have been assigned to the same abstract name and the sorts
         *  are equal.
         */
        @Override
        public MatchConditions match(LogicVariable op, SVSubstitute subst,
                MatchConditions mc, Services services) {
            if (subst == op) {
                return mc;
            }
            if (subst instanceof LogicVariable) {
                final LogicVariable lv = (LogicVariable) subst;
                if(lv.sort() == op.sort() 
                        && mc.renameTable().sameAbstractName(op, lv)) {
                    return mc;
                }
            }
            return null;
        }

    } 


    private static class ModalOperatorSVMatcher extends AbstractSVMatcher<ModalOperatorSV> {

        @Override
        public MatchConditions match(ModalOperatorSV op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {        
            if (!(subst instanceof Modality)) {
                Debug.out("FAILED. ModalOperatorSV matches only modalities " +
                        "(template, orig)",
                        op, subst);
                return null;
            }                

            final Modality m = (Modality) subst;
            if(op.getModalities().contains(m)) {
                Operator o = (Operator) mc.getInstantiations().getInstantiation(op);
                if(o == null) {
                    return mc.setInstantiations(mc.getInstantiations().add(op, m, services));
                } else if(o != m) {
                    Debug.out("FAILED. Already instantiated with a different operator.");
                    return null;
                } else {
                    return mc;
                }
            }

            Debug.out("FAILED. template is a schema operator,"
                    +" term is an operator, but not a matching one");
            return null; 
        }

    }


    private static class ProgramSVMatcher extends AbstractSVMatcher<ProgramSV> {

        @Override
        public MatchConditions match(ProgramSV op, 
                SVSubstitute substitute, 
                MatchConditions mc, Services services) {

            final ProgramSVSort svSort = (ProgramSVSort)op.sort();

            if (substitute instanceof Term && svSort.canStandFor((Term)substitute)) {
                return addInstantiation(op, (Term)substitute, mc, services);
            } else if (substitute instanceof ProgramElement && 
                    svSort.canStandFor((ProgramElement)substitute, 
                            mc.getInstantiations().getExecutionContext(), services)) {
                return addInstantiation(op, (ProgramElement)substitute, mc, services);
            }        
            Debug.out("FAILED. Cannot match ProgramSV with given " +
                    "instantiation(template, orig)", op, substitute);
            return null;
        }


    }

    private static class SkolemTermSVMatcher extends AbstractSVMatcher<SkolemTermSV> {

        @Override
        public MatchConditions match(SkolemTermSV op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {
            if(subst.equals(mc.getInstantiations().getInstantiation(op))) {
                return mc;
            } else {
                return null;
            }
        }
    }

    private static class SortDependingFunctionMatcher extends ElementMatcher<SortDependingFunction> {

        /**
         * tries to match sort <code>s1</code> to fit sort <code>s2</code>
         * @param s1 Sort tried to matched (maybe concrete or (contain) generic)
         * @param s2 concrete Sort 
         * @param mc the MatchConditions up to now
         * @return <code>null</code> if failed the resulting match conditions 
         * otherwise 
         */
        private static MatchConditions matchSorts(Sort s1, 
                Sort s2, 
                MatchConditions mc,
                Services services) {
            // This restriction has been dropped for free generic sorts to prove taclets correct
            //            assert !(s2 instanceof GenericSort)
            //                   : "Sort s2 is not allowed to be of type generic.";
            if (!(s1 instanceof GenericSort)) {
                if (s1 == s2) {
                    return mc;
                } else {
                    Debug.out("FAIL. Sorts not identical.", s1, s2);
                    return null;
                }
            } else {        
                final GenericSort gs = (GenericSort)s1;
                final GenericSortCondition c 
                = GenericSortCondition.createIdentityCondition(gs, s2);                                               
                if(c == null) {
                    Debug.out("FAILED. Generic sort condition");
                    return null;
                } else {
                    try {                   
                        mc = mc.setInstantiations(mc.getInstantiations()
                                .add(c, services));
                    } catch(SortException e) {
                        Debug.out("FAILED. Sort mismatch.", s1, s2);
                        return null;
                    }
                }                  
            }               
            return mc;
        }

        /**
         * Taking this sortdepending function as template to be matched against <code>op</code>, 
         * the necessary conditions are returned or null if not unifiable (matchable).
         * A sortdepending function is matched successfully against another sortdepending function
         * if the sorts can be matched and they are of same kind.      
         */
        @Override    
        public MatchConditions match(SortDependingFunction op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {  
            if(!(subst instanceof SortDependingFunction)) {
                Debug.out("FAILED. Given operator cannot be matched by a sort" +
                        "depending function (template, orig)", op, subst);
                return null;
            }

            final SortDependingFunction sdp = (SortDependingFunction)subst;   
            if(!op.isSimilar(sdp)) {
                Debug.out("FAILED. Sort depending symbols not similar.", op, subst);
                return null;
            }

            final MatchConditions result =  matchSorts(op.getSortDependingOn(), 
                    sdp.getSortDependingOn(), 
                    mc,
                    services);        
            if (result == null) {
                Debug.out("FAILED. Depending sorts not unifiable.", op, subst);
                return null;
            }

            return result;
        }


    }


    private static class TermLabelSVMatcher extends AbstractSVMatcher<TermLabelSV> {

        @Override
        public MatchConditions match(TermLabelSV op, SVSubstitute subst,
                MatchConditions mc, Services services) {
            if (!(subst instanceof Term)) {
                return null;
            }

            final Term t = (Term)subst;
            /*if (!t.hasLabels()) { statements about the non-existence
            return null;        of term labels should also be
        }                       possible.*/
            final SVInstantiations svInsts = mc.getInstantiations();
            final TermLabelInstantiationEntry inst =
                    (TermLabelInstantiationEntry) svInsts.getInstantiation(op);
            if (inst != null) {
                assert inst.getInstantiation() instanceof ImmutableArray<?>;
                for (Object o: (ImmutableArray<?>)inst.getInstantiation()) {
                    assert o instanceof TermLabel;
                    if (!t.containsLabel((TermLabel)o)) {
                        return null;
                    } 
                }
                return mc;
            }
            return mc.setInstantiations(svInsts.add(op, t.getLabels(), services));
        }
    }

    private static class TermSVMatcher extends AbstractSVMatcher<TermSV> {
        @Override
        public MatchConditions match(TermSV op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {   
            if(subst instanceof Term) {
                return addInstantiation(op, (Term) subst, mc, services);
            }
            Debug.out("FAILED. Schemavariable of this kind only match terms.");
            return null;
        }
    }

    private static class UpdateSVMatcher extends AbstractSVMatcher<UpdateSV> {

        @Override
        public MatchConditions match(UpdateSV op, 
                SVSubstitute subst,
                MatchConditions mc, Services services) {
            if (subst instanceof Term) {
                return addInstantiation(op, (Term) subst, mc, services);
            }
            Debug.out("FAILED. Schemavariable of this kind only match terms.");
            return null;
        }
    }

    private static class VariableSVMatcher extends AbstractSVMatcher<VariableSV> {

        @Override
        public MatchConditions match(VariableSV op, 
                SVSubstitute subst, 
                MatchConditions mc, Services services) {                
            final Term substTerm;
            if(subst instanceof LogicVariable) {
                substTerm = services.getTermBuilder().var((LogicVariable)subst);
            } else if(subst instanceof Term && 
                    ((Term)subst).op() instanceof QuantifiableVariable) {
                substTerm = (Term) subst;
            } else {
                Debug.out("Strange Exit of match in VariableSV. Check for bug");
                return null;
            }

            final Term foundMapping 
            = (Term)mc.getInstantiations().getInstantiation(op);
            if(foundMapping == null) {
                return addInstantiation(op, substTerm, mc, services);
            } else if (foundMapping.op() == substTerm.op()) {
                return mc;
            } else {
                Debug.out("FAILED. Already instantiated with different variable.");
                return null;        
            }
        } 


    }


    public abstract MatchConditions match(T op, SVSubstitute subst, MatchConditions mc, Services services);


}
