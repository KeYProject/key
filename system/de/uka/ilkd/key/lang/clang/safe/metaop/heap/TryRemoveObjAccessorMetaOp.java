package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries removing accessors at the top-level 
 * of the only parameter term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryRemoveObjAccessorMetaOp extends BaseClangMetaOp {

        public TryRemoveObjAccessorMetaOp() {
                super(new Name("#ClangTryRemoveObjAccessor"), 1);
        }
        
        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangEnvironment context) {
                Term objTerm = term.sub(0);
                
                if (objTerm.op() instanceof RepositoryFunction)
                        return objTerm; 

                if (objTerm.op() instanceof ArrayRepositoryFunction)
                        return objTerm; 

                if (objTerm.op() instanceof MemberFunction) {
                        Term structuredTerm = objTerm.sub(0);
                        return structuredTerm;
                }
                        
                if (objTerm.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm.sub(0);
                        return arrayTerm;
                }
                
                return objTerm;
        }
}
