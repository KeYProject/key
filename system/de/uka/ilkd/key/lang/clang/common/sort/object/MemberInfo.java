package de.uka.ilkd.key.lang.clang.common.sort.object;

/**
 * Structured sort member informaion.
 * 
 * @author oleg.myrk@gmail.com
 */
public class MemberInfo {
        private final String id;

        private final IInstantiableObjectSort sort;

        private final int order;

        /**
         * Creates member information.
         * 
         * @param id
         *                member id
         * @param sort
         *                member sort
         * @param order
         *                member order index (0-based)
         */
        public MemberInfo(String id, IInstantiableObjectSort sort, int order) {
                this.id = id;
                this.sort = sort;
                this.order = order;
        }

        /**
         * Returns the identifier of the member.
         * 
         * @return
         */
        public String getId() {
                return id;
        }

        /**
         * Returns the sort of the member.
         * 
         * @return
         */
        public IInstantiableObjectSort getSort() {
                return sort;
        }

        /**
         * Returns the order index of the member (0-based).
         * 
         * @return
         */
        public int getOrder() {
                return order;
        }
}
