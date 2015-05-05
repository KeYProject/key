package de.uka.ilkd.key.symbolic_execution.slicing;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Represents a location like a local variable, method parameter, static field
 * or an instance field on a specified object.
 * @author Martin Hentschel
 */
public class Location {
   /**
    * The {@link Access} path. 
    */
   private final ImmutableList<Access> accesses;

   /**
    * Constructor.
    * @param accesses The {@link Access} path.
    */
   public Location(ImmutableList<Access> accesses) {
      assert accesses != null;
      this.accesses = accesses;
   }

   /**
    * Constructor.
    * @param accesses The {@link Access} path.
    */
   public Location(Access... accesses) {
      assert accesses != null;
      this.accesses = ImmutableSLList.<Access>nil().append(accesses);
   }

   /**
    * Returns the {@link Access} path. 
    * @return The {@link Access} path. 
    */
   public ImmutableList<Access> getAccesses() {
      return accesses;
   }
   
   /**
    * Returns the access depth.
    * @return The access depth.
    */
   public int getDepth() {
      return accesses.size();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      int hashcode = 5;
      hashcode = hashcode * 17 + (accesses != null ? accesses.hashCode() : 0);
      return hashcode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof Location) {
         Location other = (Location) obj;
         return ObjectUtil.equals(accesses, other.getAccesses());
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      StringBuffer sb = new StringBuffer();
      boolean afterFirst = false;
      for (Access access : accesses) {
         if (afterFirst) {
            sb.append('.');
         }
         else {
            afterFirst = true;
         }
         sb.append(access);
      }
      return sb.toString();
   }

   /**
    * Creates a new {@link Location} in which the sub is appended.
    * @param sub The {@link Location} to append.
    * @return The new {@link Location}.
    */
   public Location append(Location sub) {
      return new Location(accesses.append(sub.getAccesses()));
   }

   /**
    * Creates a new {@link Location} in which the sub is appended.
    * @param sub The {@link Access} to append.
    * @return The new {@link Location}.
    */
   public Location append(Access sub) {
      return new Location(accesses.append(sub));
   }

   /**
    * Converts this {@link Location} into a {@link Term}.
    * @param services The {@link Services} to use.
    * @return The created {@link Term}.
    */
   public Term toTerm(Services services) {
      Term parent = null;
      for (Access access : accesses) {         
         if (access.isArrayIndex()) {
            // Special handling for array indices.
            assert parent != null;
            assert access.getDimensionExpressions().size() == 1;
            parent = services.getTermBuilder().dotArr(parent, access.getDimensionExpressions().get(0));
         }
         else if (SymbolicExecutionUtil.isStaticVariable(access.getProgramVariable())) {
            // Static field access
            assert parent == null;
            Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)access.getProgramVariable(), services);
            parent =  services.getTermBuilder().staticDot(access.getProgramVariable().sort(), function);
         }
         else if (parent == null) {
            // Direct access to a variable
            assert parent == null;
            parent = services.getTermBuilder().var(access.getProgramVariable());
         }
         else if (services.getJavaInfo().getArrayLength() == access.getProgramVariable()) {
            // Special handling for length attribute of arrays
            assert parent != null;
            Function function = services.getTypeConverter().getHeapLDT().getLength();
            parent = services.getTermBuilder().func(function, parent);
         }
         else {
            // Field access on the parent variable
            assert parent != null;
            Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)access.getProgramVariable(), services);
            parent = services.getTermBuilder().dot(access.getProgramVariable().sort(), parent, function);
         }
      }
      return parent;
   }
}