package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.logic.AnonymisingUpdateFactory;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies anonymous update to the formula passed as the
 * first argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class AnonymousUpdateMetaOp extends BaseClangMetaOp {

        public AnonymousUpdateMetaOp() {
                super(new Name("#ClangAnonymousUpdate"), 1);
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
        protected Term calculate(Term term, 
                        IClangEnvironment context) {
                Term term0 = term.sub(0);

                UpdateFactory uf = new UpdateFactory((Services)context.getLangServicesEnv().getMainServices(),
                                new UpdateSimplifier());
                AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);

                return auf
                                .createAnonymisingUpdateTerm(
                                                SetAsListOfLocationDescriptor.EMPTY_SET
                                                                .add(EverythingLocationDescriptor.INSTANCE),

                                                term0,
                                                (Services)context.getLangServicesEnv().getMainServices());

        }
}
