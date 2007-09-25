package de.uka.ilkd.key.lang.clang.common.walker;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.programmeta.IClangProgramMeta;
import de.uka.ilkd.key.lang.common.program.ArrayOfIProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.walker.BaseCreatingWalker;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replaces program schema variables in a template program element with their
 * instantiations and also executes program meta constructs.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ProgramInstantiator extends BaseCreatingWalker {

        private final IProgramElement root;

        private final IClangEnvironment environment;

        private final SVInstantiations svInstantiations;

        private IProgramElement result = null;

        public ProgramInstantiator(IProgramElement root,
                        IClangEnvironment environment,
                        SVInstantiations svInstantiations) {
                this.root = root;
                this.environment = environment;
                this.svInstantiations = svInstantiations;
        }

        public void start() {
                walk(root);
                result = (IProgramElement) (peek()).get(IProgramElement.class);
        }

        public IProgramElement result() {
                return result;
        }

        protected void doDefaultAction(IProgramElement programElement) {
                super.doDefaultAction(programElement);
        }

        protected void doAction(IProgramElement programElement) {
                if (programElement instanceof BaseProgramSV)
                        doActionOnSchemaVariable((BaseProgramSV) programElement);
                else if (programElement instanceof IClangProgramMeta)
                        doActionOnProgramMeta((IClangProgramMeta) programElement);
                else
                        super.doAction(programElement);
        }

        protected void doActionOnSchemaVariable(BaseProgramSV sv) {
                final Object inst = svInstantiations.getInstantiation(sv);
                if (inst instanceof IProgramElement) {
                        pop();
                        addChild((IProgramElement) inst);
                        markChanged();
                } else if (inst instanceof ArrayOfIProgramElement) {
                        pop();
                        addChildren((ArrayOfIProgramElement) inst);
                        markChanged();
                } else
                        throw new IllegalStateException(
                                        "Instantiation missing for schema variable: "
                                                        + sv);
        }

        protected void doActionOnProgramMeta(IClangProgramMeta programMeta) {
                IProgramElement programMetaResult = programMeta.execute(
                                environment, svInstantiations);
                pop();
                addChild(programMetaResult);
                markChanged();
        }
}
