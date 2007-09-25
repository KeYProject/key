package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * CDL arithmetic integer sort.
 * @author oleg.myrk@gmail.com
 */
public class IntegerSort extends ArithmeticSort {
        
        /**
         * Int sort to use.
         */
        private final Sort intSort;
        
        /**
         * Constant <code>{this}::MIN</code> associated with this type instance.
         */
        private MinConstant minConstant;

        /**
         * Constant <code>{this}::MAX</code> associated with this type instance.
         */
        private MaxConstant maxConstant;
        
        /**
         * Function <code>{this}::fromInt</code> associated with this type instance.
         */        
        private FromIntFunction fromIntFunction;
        
        /**
         * Function <code>{this}::toInt</code> associated with this type instance.
         */        
        private ToIntFunction toIntFunction;
        
        /**
         * Creates arithmetic integer sort with given name.
         * @param id
         * @parma valueMarkerSort
         */
        public IntegerSort(String id, Sort intSort, ValueMarkerSort valueMarkerSort) {
                super(id, valueMarkerSort); 
                this.intSort = intSort;
        }
        
        /**
         * Returns constant <code>{this}::MIN</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public MinConstant getMinConstant() {
                return minConstant;
        }
        
        /**
         * Returns constant <code>{this}::MAX</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public MaxConstant getMaxConstant() {
                return maxConstant;
        }
        
        /**
         * Returns function <code>{this}::fromInt</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public FromIntFunction getFromIntFunction() {
                return fromIntFunction;
        }
        
        /**
         * Returns function <code>{this}::toInt</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public ToIntFunction getToIntFunction() {
                return toIntFunction;
        }        
        
        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.minConstant = new MinConstant(this, intSort);
                sortBuilder.getFunctionNS().add(minConstant);
                
                this.maxConstant = new MaxConstant(this, intSort);
                sortBuilder.getFunctionNS().add(maxConstant);
                
                this.fromIntFunction = new FromIntFunction(this, intSort);
                sortBuilder.getFunctionNS().add(fromIntFunction);                
                
                this.toIntFunction = new ToIntFunction(this, intSort);
                sortBuilder.getFunctionNS().add(toIntFunction);                
        }
}
