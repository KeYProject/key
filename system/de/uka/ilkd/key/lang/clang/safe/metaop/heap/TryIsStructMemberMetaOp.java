package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Meta operation that tries to evaluate expression <code>isStructMember(o)</code>, 
 * where <code>o</code> is of object type. Evaluation is based on removing accessors
 * at the top-level of term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryIsStructMemberMetaOp extends SafeBaseMetaOp {

        public TryIsStructMemberMetaOp() {
                super(new Name("#ClangTryIsStructMember"), 1);
        }

        /**
         * @inheritDocs
         */
        public Sort sort(Term[] term) {
                return Sort.FORMULA;
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("isStructMember")))
                        throw new IllegalArgumentException("#TryIsStructMember first argument must be 'isStructMember' predicate");

                Term isStructMemberTerm = term.sub(0);
                Term objTerm = isStructMemberTerm.sub(0);
                
                if (objTerm.op() instanceof RepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE); 

                if (objTerm.op() instanceof ArrayRepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE); 

                if (objTerm.op() instanceof MemberFunction && ((MemberFunction)objTerm.op()).getStructuredSort() instanceof StructSort) 
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
                        
                if (objTerm.op() instanceof ElemFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE);
                
                if (objTerm.op() == symbolEnv.getNullConstant())
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE);
                
                return isStructMemberTerm;
        }
}
