package de.uka.ilkd.key.lang.clang.common.walker;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.lang.common.program.BaseVariable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.walker.BaseWalker;

/**
 * Collects all program variables in a root program element.
 */
public class VariableCollector extends BaseWalker {

        private final IProgramElement root;
        private final HashSet result = new HashSet();

        /**
         * Collects all program variables occuring in the AST <tt>root</tt>
         * 
         * @param root
         *                the ProgramElement which is the root of the AST
         */
        public VariableCollector(IProgramElement root) {
                this.root = root;
        }

        /**
         * Starts the collecting process.
         */
        public void start() {
                walk(root);
        }

        /**
         * Returns the set of collected variables.
         * @return
         */
        public Set result() {
                return result;
        }
        
        /**
         * @inheritDocs
         */
        protected void doAction(IProgramElement node) {
                if (node instanceof BaseVariable)
                        result.add(node);                
        }
}
