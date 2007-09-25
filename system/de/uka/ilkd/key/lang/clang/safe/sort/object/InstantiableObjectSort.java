package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetOfSort;

/**
 * CDL instantiable object sort that has a repository function.
 * 
 * TODO: We should split this into an interface <code>IInstantiableObjectSort</code>
 * and a base class <code>BaseInstantiableObjectSort</code>, but we do not have an
 * interface <code>IClangObjectSort</code> so there is no point for now.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class InstantiableObjectSort extends BaseObjectSort implements IInstantiableObjectSort {
        /**
         * Repository function <code>&lt;lookup&gt;</code> associated with this type instance. 
         */
        private RepositoryFunction repositoryFunction;
        
        /**
         * Creates instantiable object sort.
         * @param name
         * @param extendsSorts
         */
        public InstantiableObjectSort(Name name, SetOfSort extendsSorts) {
                super(name, extendsSorts);
        }
        
        /**
         * Returns repository function <code>&ltlookup&gt</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public RepositoryFunction getRepositoryFunction() {
                return repositoryFunction;
        }

        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.repositoryFunction = new RepositoryFunction(this, sortBuilder.getIntSort());
                sortBuilder.getFunctionNS().add(repositoryFunction);
        } 
}
