package org.key_project.key4eclipse.resources.io;

import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * An assumption made during proof an saved in a proof meta file.
 * Examples for assumptions are used specifications of classes in the
 * boot class path or an class path entry.
 * @author Martin Hentschel
 */
public class ProofMetaFileAssumption {
   /**
    * The kind.
    */
   private final String kind;

   /**
    * The name.
    */
   private final String name;

   /**
    * The target.
    */
   private final String target;
   
   /**
    * The type.
    */
   private final String type;

   /**
    * Constructor.
    * @param kind The kind.
    * @param name The name.
    * @param target The target.
    * @param type The type.
    */
   public ProofMetaFileAssumption(String kind, String name, String target, String type) {
      this.kind = kind;
      this.name = name;
      this.target = target;
      this.type = type;
   }

   /**
    * Returns the kind.
    * @return The kind.
    */
   public String getKind() {
      return kind;
   }

   /**
    * Returns the name.
    * @return The name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the target.
    * @return The target.
    */
   public String getTarget() {
      return target;
   }

   /**
    * Returns the type.
    * @return The type.
    */
   public String getType() {
      return type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      int hashcode = 5;
      hashcode = hashcode * 17 + ObjectUtil.hashCode(kind);
      hashcode = hashcode * 17 + ObjectUtil.hashCode(name);
      hashcode = hashcode * 17 + ObjectUtil.hashCode(target);          
      hashcode = hashcode * 17 + ObjectUtil.hashCode(type);
      return hashcode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof ProofMetaFileAssumption) {
         ProofMetaFileAssumption other = (ProofMetaFileAssumption)obj;
         return ObjectUtil.equals(kind, other.getKind()) &&
                ObjectUtil.equals(name, other.getName()) &&
                ObjectUtil.equals(target, other.getTarget()) &&
                ObjectUtil.equals(type, other.getType());
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
      if (IProofReference.USE_AXIOM.equals(kind)) {
         return "Axiom " + target + " of " + type + " fulfills its contract (" + name + ").";
      }
      else if (IProofReference.USE_INVARIANT.equals(kind)) {
         return "Invariant " + name + " of " + type + " holds.";
      }
      else if (IProofReference.USE_CONTRACT.equals(kind)) {
         return "Method " + target + " of " + type + " fulfills its method contract (" + name + ").";
      }
      else {
         return "kind = " + kind +
                ", name = " + name +
                ", target = " + target +
                ", type = " + type;
      }
   }
}
