package de.uka.ilkd.key.lang.clang.common.walker;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.walker.BaseWalker;

/**
 * Collects program variables introduces by the declarations in a root program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntroducedVariableCollector extends BaseWalker {
        private final IProgramElement root;
        private final HashSet result = new HashSet();

        public IntroducedVariableCollector(IProgramElement root) {
                this.root = root;
        }
        
        /**
         * Starts the collection process.
         */
        public void start() {
                walk(root);
        }

        /**
         * Returns the collection result.
         * @return
         */
        public Set result() {
                return result;
        }

        /**
         * @inheritDocs
         */
        protected void doAction(IProgramElement node) {
                if (node instanceof VariableDeclaration)
                        result.add(((VariableDeclaration)node).getVariable());
        }
}
