package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries to evaluate expression <code>rootObjLookupIdx(o)</code>, 
 * where <code>o</code> is of object type. Evaluation is based on removing accessors
 * at the top-level of term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryRootObjLookupIdxMetaOp extends SafeBaseMetaOp {

        public TryRootObjLookupIdxMetaOp() {
                super(new Name("#ClangTryRootObjLookupIdx"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("rootObjLookupIdx")))
                        throw new IllegalArgumentException("#TryRootObjLookupIdx first argument must be 'rootObjLookupIdx' function");

                Term rootObjLookupIdxTerm = term.sub(0);
                Term objTerm = rootObjLookupIdxTerm.sub(0);
                
                if (objTerm.op() instanceof RepositoryFunction) {
                        Term lookupIdx = objTerm.sub(0);
                        return lookupIdx;
                }

                if (objTerm.op() instanceof ArrayRepositoryFunction) {
                        Term lookupIdx = objTerm.sub(0);
                        return lookupIdx;
                }

                if (objTerm.op() instanceof MemberFunction)
                        return rootObjLookupIdxTerm;
                        
                if (objTerm.op() instanceof ElemFunction)
                        return rootObjLookupIdxTerm;
                
                if (objTerm.op() == symbolEnv.getNullConstant())
                        return rootObjLookupIdxTerm;
                
                return rootObjLookupIdxTerm;
        }
}
