package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContract.Terms;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import java.util.Collection;
import java.util.EnumMap;


/**
 * Immutable class.
 * <p/>
 * @author christoph
 */
class BasicSnippetData {

    /**
     * Tells whether the contract contains a measured_by clause.
     */
    final boolean hasMby;
    /**
     * Returns the contracted function symbol.
     */
    final IObserverFunction targetMethod;
    /**
     * Returns the contracted block.
     */
    final StatementBlock targetBlock;
    /**
     * Returns the KeYJavaType representing the class/interface to which the
     * specification element belongs.
     */
    final KeYJavaType forClass;
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

        PRECONDITION(Term.class),
        POSTCONDITION(Term.class),
        MODIFIES(Term.class),
        DEPENDENS(Term.class),
        MEASURED_BY(Term.class),
        MODALITY(Modality.class),
        RESPECTS(Term[][].class),
        DECLASSIFIES(Term[][].class);
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
        this.hasMby = contract.hasMby();
        this.targetMethod = contract.getTarget();
        this.targetBlock = null;
        this.forClass = contract.getKJT();
        this.tb = new TermBuilder.Serviced(services);

        contractContents.put(Key.PRECONDITION, contract.getPre());
        contractContents.put(Key.POSTCONDITION, contract.getPost());
        contractContents.put(Key.MODIFIES, contract.getMod());
        contractContents.put(Key.MEASURED_BY, contract.getMby());
        contractContents.put(Key.MODALITY, contract.getModality());

        final Term heap = TermBuilder.DF.getBaseHeap(services);
        origVars =
                new ProofObligationVars(contract.getSelf(),
                                        contract.getParams(), contract.getResult(), contract.getExc(),
                                        heap, services);

    }


    BasicSnippetData(InformationFlowContract contract,
                     Services services) {
        this.hasMby = contract.hasMby();
        this.targetMethod = contract.getTarget();
        this.targetBlock = null;
        this.forClass = contract.getKJT();
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
        origVars =
                new ProofObligationVars(contract.getSelf(),
                                        contract.getParams(), contract.getResult(),
                                        contract.getExc(), heap, services);

    }


    BasicSnippetData(BlockContract contract,
                     Services services) {
        this.hasMby = contract.hasMby();
        this.targetMethod = contract.getTarget();
        this.targetBlock = contract.getBlock();
        this.forClass = contract.getKJT();
        this.tb = new TermBuilder.Serviced(services);


        contractContents.put(Key.PRECONDITION, contract.getPre(services));
        contractContents.put(Key.MODIFIES, contract.getMod(services));
        contractContents.put(Key.MODALITY, contract.getModality());
        contractContents.put(Key.RESPECTS,
                             doubleListToArray(contract.getRespects()));
        contractContents.put(Key.DECLASSIFIES,
                             doubleListToArray(contract.getDeclassifies()));

        final Term heapTerm = TermBuilder.DF.getBaseHeap(services);
        Terms vars = contract.getVariablesAsTerms();
        origVars =
                new ProofObligationVars(vars.self, ImmutableSLList.<Term>nil(),
                                        vars.result, vars.exception, heapTerm, services);

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
