package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.HashMapFromStringToMemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.IteratorOfMemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that creates update representing deep copy <code>{#param1 :> #param2}#param3</code>
 * of struct sort.
 * 
 * @author oleg.myrk@gmail.com
 */
public class DeepUpdateMetaOp extends BaseClangMetaOp {

        public DeepUpdateMetaOp() {
                super(new Name("#ClangDeepUpdate"), 3);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                Term term2 = term.sub(2);
                if (!(term0.sort() == term1.sort() && term0.sort() instanceof StructSort))
                        throw new RuntimeException(
                                        "#ClangDeepUpdate should be applied to two terms of the same struct sort");
                StructSort structSort = ((StructSort)term0.sort());
                
                ListOfTerm[] update = buildUpdate(structSort, term0, term1, new ListOfTerm[]{ SLListOfTerm.EMPTY_LIST, SLListOfTerm.EMPTY_LIST} );
                return TermFactory.DEFAULT.createUpdateTerm(update[0].toArray(), update[1].toArray(), term2);
        }
        
        private ListOfTerm[] buildUpdate(StructSort structSort, Term term0, Term term1, ListOfTerm[] update) {
                HashMapFromStringToMemberFunction memberFunctionMap = structSort.getMemberFunctionMap();
                
                for(IteratorOfMemberFunction i = memberFunctionMap.values(); i.hasNext();) {
                        MemberFunction memberFunction = (MemberFunction)i.next();
                        
                        Term childTerm0 = TermFactory.DEFAULT.createFunctionTerm(memberFunction, term0);
                        Term childTerm1 = TermFactory.DEFAULT.createFunctionTerm(memberFunction, term1);
                        
                        Sort memberSort = memberFunction.sort();
                        
                        if (memberSort instanceof IScalarSort) {
                                update[0] = update[0].append(TermFactory.DEFAULT.createFunctionTerm(((ScalarSort)memberSort).getValueLocation(), childTerm0));
                                update[1] = update[1].append(TermFactory.DEFAULT.createFunctionTerm(((ScalarSort)memberSort).getValueLocation(), childTerm1));
                        }
                        else if (memberSort instanceof StructSort)
                                update = buildUpdate((StructSort)memberSort, childTerm0, childTerm1, update);
                        else
                                assert(false);
                }
                
                return update;
        }
}
