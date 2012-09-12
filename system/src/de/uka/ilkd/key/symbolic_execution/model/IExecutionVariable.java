package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;

/**
 * <p>
 * A variable value pair contained in an {@link IExecutionStateNode}, e.g.
 * the method parameter {@code int x = 42}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionVariable} which
 * is instantiated lazily by the {@link IExecutionStateNode} implementations.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionStateNode
 * @see ExecutionVariable
 */
public interface IExecutionVariable extends IExecutionElement {
   /**
    * Returns the {@link IProgramVariable} which contains the represented value.
    * @return The {@link IProgramVariable} which contains the represented value.
    */
   public IProgramVariable getProgramVariable();
   
   /**
    * <p>
    * Checks if the value is unknown.
    * </p>
    * <p>
    * Imagine the following class:
    * <pre><code>
    * public class A {
    *    private A next;
    *    
    *    public int main() {
    *       return 42; // breakpoint
    *    }
    * }
    * </code></pre>
    * If the main method is debugged symbolically and stopped at the statement
    * marked with the comment {@code // breakpoint} the field {@code self.next}
    * has the symbolic value {@code SVself.next}. And its field 
    * {@code self.next.next} has again a symbolic value {@code SVself.next.next}.
    * This chain is infinite deep. But on the other side the Sequent contains
    * no information about {@code self.next} so the symbolic value can be
    * {@code null} or a concrete object. Such symbolic values which are not
    * founded in the Sequent are treated in the symbolic execution API as
    * "unknown" to avoid infinite deep value hierarchies if they are not cyclic.
    * </p>
    * @return {@code true} value is unknown, {@code false} value is known.
    */
   public boolean isValueUnknown() throws ProofInputException;
   
   /**
    * Returns the value of the variable.
    * @return The value of the variable.
    */
   public Term getValue() throws ProofInputException;
   
   /**
    * Returns the value of the variable as human readable string representation.
    * @return The value of the variable as human readable string representation.
    */
   public String getValueString() throws ProofInputException;
   
   /**
    * <p>
    * Checks if the value represents an object or an attribute of the object 
    * defined by the parent {@link IExecutionVariable}. 
    * </p>
    * <p>
    * All values which are not a basic datatype (integer, boolean, ...) and
    * not an instance of a library class will be treated as object.
    * </p>
    * @return {@code true} is an object, {@code false} is an attribute of the object defined by the parent {@link IExecutionVariable}.
    * @throws ProofInputException Occurred Exception.
    */
   public boolean isValueAnObject() throws ProofInputException;
   
   /**
    * Returns the type of the variable as human readable string.
    * @return The type of the variable as human readable string.
    */
   public String getTypeString() throws ProofInputException;
   
   /**
    * Returns the parent {@link IExecutionVariable}.
    * @return The parent {@link IExecutionVariable}.
    */
   public IExecutionVariable getParentVariable();
   
   /**
    * Returns contained child variables which forms complex data types.
    * @return The contained child variables.
    */
   public IExecutionVariable[] getChildVariables() throws ProofInputException;
   
   /**
    * Returns the index in the parent array if an array cell value is represented.
    * @return The index in the parent array or {@code -1} if no array cell value is represented.
    */
   public int getArrayIndex();
   
   /**
    * Checks if the current value is part of a parent array.
    * @return {@code true} is array cell value, {@code false} is a "normal" value.
    */
   public boolean isArrayIndex();
}
