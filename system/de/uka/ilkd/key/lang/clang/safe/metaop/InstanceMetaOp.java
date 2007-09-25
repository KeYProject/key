package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.InstanceofSymbol;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::instance</code> to its 
 * first argument, while type type T is taken from the second argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class InstanceMetaOp extends SafeBaseMetaOp {

        public InstanceMetaOp() {
                super(new Name("#ClangInstance"), 2);
        }
                
        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                
                if (!(term1.sort() instanceof AbstractSort))
                        throw new RuntimeException(
                                "#ClangInstance applied to the second term that does not have instanceof function");
                
                AbstractSort abstractSort = (AbstractSort)term1.sort();
                InstanceofSymbol instanceFunction = (InstanceofSymbol)abstractSort.lookupSymbol(new Name("instance"));
                
                return TermFactory.DEFAULT.createFunctionTerm(instanceFunction, term0);
        }
}
