package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.SpecificationElement;

import java.util.EnumMap;

/**
 * Immutable class.
 * @author christoph
 */
class BasicSnippetData {
    
    /**
     * The contract for which the snippets are produced.
     */
    final Contract contract;
    
    /**
     * The loop invariant for which the snippets are produced (then contract is set to null).
     */
    final LoopInvariant invariant;
    // FIXME: Until now this is a workaround, has to be done more nicely!
    
    /**
     * Variables originally used during parsing.
     */
    final ProofObligationVars origVars;
    
    /**
     * TermBuilder used by the FactoryMethods.
     */
    final TermBuilder.Serviced tb;

    /**
     * Unified contract content.
     */
    private final EnumMap<Key, Object> contractContents =
            new EnumMap<Key, Object>(Key.class) {

        @Override
        public Object put(Key key,
                          Object value) {
            assert value == null || key.getType().isInstance(value);
            return super.put(key, value);
        }
    };


    /**
     * Keys to access the unified contract content.
     */
    static enum Key {
        PRECONDITION (Term.class),
        POSTCONDITION (Term.class),
        MODIFIES (Term.class),
        DEPENDENS (Term.class),
        MEASURED_BY (Term.class),
        MODALITY (Modality.class),
        RESPECTS (Term[][].class),
        DECLASSIFIES (Term[][].class);

        private final Class type;
        Key(Class type) {
            this.type = type;
        }

        public Class getType() {
            return type;
        }
    };


    BasicSnippetData(FunctionalOperationContract contract,
                     Services services) {
        this.contract = contract;
        this.invariant = null;
        this.tb = new TermBuilder.Serviced(services);

        contractContents.put(Key.PRECONDITION, contract.getPre());
        contractContents.put(Key.POSTCONDITION, contract.getPost());
        contractContents.put(Key.MODIFIES, contract.getMod());
        contractContents.put(Key.MEASURED_BY, contract.getMby());
        contractContents.put(Key.MODALITY, contract.getModality());

        final Term heap = TermBuilder.DF.getBaseHeap(services);
        origVars = new ProofObligationVars(contract.getSelf(), null,
                contract.getParams(), contract.getResult(), null,
                contract.getExc(), null, heap, null, null, "", services);

    }
    
    BasicSnippetData(LoopInvariant invariant, Services services) {
        this.invariant = invariant;
        this.contract = null;
        this.tb = new TermBuilder.Serviced(services);
        
        contractContents.put(Key.PRECONDITION, invariant);
        contractContents.put(Key.POSTCONDITION, null);
        contractContents.put(Key.MODIFIES, invariant.getModifies());
        contractContents.put(Key.MEASURED_BY, null);
        contractContents.put(Key.MODALITY, null);

        
        final Term heap = TermBuilder.DF.getBaseHeap(services);
        origVars = new ProofObligationVars(invariant.getInternalSelfTerm(), null,
                invariant.getParams(), invariant.getResults(), null,
                null, null, heap, null, null, "", services);

    }


    BasicSnippetData(InformationFlowContract contract,
                     Services services) {
        this.contract = contract;
        this.invariant = null;
        this.tb = new TermBuilder.Serviced(services);

        
        contractContents.put(Key.PRECONDITION, contract.getPre());
        contractContents.put(Key.MODIFIES, contract.getMod());
        contractContents.put(Key.DEPENDENS, contract.getDep());
        contractContents.put(Key.MEASURED_BY, contract.getMby());
        contractContents.put(Key.MODALITY, contract.getModality());
        contractContents.put(Key.RESPECTS,
                             doubleListToArray(contract.getRespects()));
        contractContents.put(Key.DECLASSIFIES,
                             doubleListToArray(contract.getDeclassifies()));
        
        final Term heap = TermBuilder.DF.getBaseHeap(services);
        origVars = new ProofObligationVars(contract.getSelf(), null,
                contract.getParams(), contract.getResult(), null,
                contract.getExc(), null, heap, null, null, "", services);

    }
    
    
    private Term[][] doubleListToArray(ImmutableList<ImmutableList<Term>> termss) {
        Term[][] result = new Term[termss.size()][];
        int i = 0;
        for (ImmutableList<Term> terms : termss) {
            result[i] = terms.toArray(Term.class);
            i++;
        }
        return result;
    }
    
    
    Object getContractContent(Key contentKey) {
        return contractContents.get(contentKey);
    }
}
