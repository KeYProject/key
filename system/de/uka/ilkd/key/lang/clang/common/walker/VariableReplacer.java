package de.uka.ilkd.key.lang.clang.common.walker;

import java.util.Map;

import de.uka.ilkd.key.lang.clang.common.program.variable.Variable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.walker.BaseCreatingWalker;

/**
 * Replaces program variables in a root program element according to a mapping.
 */
public class VariableReplacer extends BaseCreatingWalker {

        private final IProgramElement root;
        private IProgramElement result = null;

        /**
         * A map from variables to be replaced to their replacements. 
         */
        protected Map replaceMap;

        /** 
         * @param programElement
         *                the statement where the program variables are replaced
         * @param repalceMap
         *                A map from variables to be replaced to their replacements.
         */
        public VariableReplacer(IProgramElement programElement, Map replaceMap) {
                this.root = programElement;
                this.replaceMap = replaceMap;
        }

        /**
         * Starts the replacement process.
         */
        public void start() {
                walk(root);
                result = (IProgramElement) peek().get(IProgramElement.class);
        }

        /**
         * Returns the result of replacement.
         * @return
         */
        public IProgramElement result() {
                return result;
        }
        
        /**
         * @inheritDocs
         */
        protected void doDefaultAction(IProgramElement programElement) {
                super.doDefaultAction(programElement);
        }
        
        /**
         * @inheritDocs
         */
        protected void doAction(IProgramElement programElement) {
                if (programElement instanceof Variable) {
                        IProgramElement newPV = (IProgramElement) replaceMap.get(programElement);
                        if (newPV != null) {
                                pop();
                                addChild(newPV);
                                markChanged();
                        } else
                                super.doAction(programElement);
                }
                else
                        super.doAction(programElement);
        }
}
