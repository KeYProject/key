package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * Instances of this interface are used to customize and extend the behavior of a {@link ProofOblInput}.
 * <p>
 * Implementations are instantiated once via {@link ProofInitServiceUtil#createOperationPOExtension(ProofOblInput)}
 * and reused all the time. This means that {@link POExtension} are singletons and should not have a state.
 * @author Martin Hentschel
 */
public interface POExtension {
   /**
    * Checks if the given {@link ProofOblInput} is supported.
    * @param po The {@link ProofOblInput} to check.
    * @return {@code true} is supported, {@code false} is not supported.
    */
   public boolean isPOSupported(ProofOblInput po);
   
   /**
    * Modifies the post condition.
    * @param proofConfig The {@link InitConfig} to use.
    * @param services The {@link Services} to use.
    * @param postTerm The post condition to modify.
    * @return The modified post condition or the original post condition if no modifications were performed.
    */
   public Term modifyPostTerm(InitConfig proofConfig, Services services, Term postTerm);
}
