package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies cast <code>(T)</code> to its first argument,
 * while type type T is taken from the second argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class CastMetaOp extends BaseClangMetaOp {

        public CastMetaOp() {
                super(new Name("#ClangCast"), 2);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);

                if (!(term1.sort() instanceof AbstractSort))
                        throw new RuntimeException(
                                        "#ClangCast applied to the second term that does not have cast function");

                return TermFactory.DEFAULT.createCastTerm((AbstractSort) term1
                                .sort(), term0);
        }
}
