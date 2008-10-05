package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Modality;


/**
 * 
 * This class implements the Visitor concept for terms, to check, wheather it contains
 * a modality, or not.
 * 
 * @author Simon Greiner
 *
 */
public class ModalityChecker extends Visitor{

        private boolean hasModality = false;
        
        @Override
        public void visit(Term visited) {
                if (!hasModality && visited.op() instanceof Modality) {
                        hasModality = true;
                }
        }
        
        public boolean hasModality() {
                return this.hasModality;
        }
        
        public void reset() {
                this.hasModality = false;
        }
                
}
