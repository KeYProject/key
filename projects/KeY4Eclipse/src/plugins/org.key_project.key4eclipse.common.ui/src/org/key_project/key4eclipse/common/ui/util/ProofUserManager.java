package org.key_project.key4eclipse.common.ui.util;

import java.util.HashSet;
import java.util.Set;
import java.util.WeakHashMap;

import org.eclipse.core.runtime.Assert;

import de.uka.ilkd.key.proof.Proof;

/**
 * This singleton class is used to manage user of a {@link Proof} to make
 * sure that a {@link Proof} is only disposed via {@link Proof#dispose()} if
 * it is no longer in use (no user available). 
 * @author Martin Hentschel
 */
public final class ProofUserManager {
   /**
    * Stores for each {@link Proof} the registered users.
    */
   private WeakHashMap<Proof, Set<Object>> proofUsers = new WeakHashMap<Proof, Set<Object>>();
   
   /**
    * The only instance of this class.
    */
   private static final ProofUserManager instance = new ProofUserManager();
   
   /**
    * Forbid multiple instances.
    */
   private ProofUserManager() {
   }
   
   /**
    * Registers the {@link Proof} with the given user if it is not already
    * registered. If it is already registered the user is added to the proof users
    * if not already present.
    * @param proof The {@link Proof}.
    * @param user The user.
    */
   public void addUser(Proof proof, Object user) {
      Assert.isNotNull(proof, "Proof not defined.");
      Assert.isNotNull(user, "User not defined.");
      synchronized (this) {
         Set<Object> users = proofUsers.get(proof);
         if (users == null) {
            users = new HashSet<Object>();
            proofUsers.put(proof, users);
         }
         users.add(user);
      }
   }
   
   /**
    * Removes the user from the registered proof users. If the proof
    * has no user anymore it is automatically disposed via {@link Proof#dispose()}.
    * @param proof The {@link Proof}.
    * @param userThe user.
    */
   public void removeUserAndDispose(Proof proof, Object user) {
      Assert.isNotNull(proof, "Proof not defined.");
      Assert.isNotNull(user, "User not defined.");
      synchronized (this) {
         Set<Object> users = proofUsers.get(proof);
         if (users != null) {
            users.remove(user);
            if (users.isEmpty()) {
               proofUsers.remove(proof);
               proof.dispose();
            }
         }
         else {
            proof.dispose();
         }
      }
   }
   
   /**
    * Returns all registered {@link Proof}s.
    * @return All registered {@link Proof}s.
    */
   public Proof[] getProofs() {
      synchronized (this) {
         Set<Proof> keys = proofUsers.keySet(); 
         return keys.toArray(new Proof[keys.size()]);
      }
   }

   /**
    * Returns all registered user of the given {@link Proof}.
    * @param proof The {@link Proof} to get its users.
    * @return The registered user of the {@link Proof}.
    */
   public Object[] getUsers(Proof proof) {
      if (proof != null) {
         synchronized (this) {
            Set<Object> users= proofUsers.get(proof); 
            return users.toArray(new Object[users.size()]);
         }
      }
      else {
         return new Object[0];
      }
   }

   /**
    * Returns the singleton instance of this class.
    * @return The singleton instance of this class.
    */
   public static ProofUserManager getInstance() {
      return instance;
   }
}
