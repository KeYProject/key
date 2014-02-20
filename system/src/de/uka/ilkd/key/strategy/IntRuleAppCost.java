package de.uka.ilkd.key.strategy;


class IntRuleAppCost extends NumberRuleAppCost {

    private final int cost;

    protected IntRuleAppCost(int p_cost) {
        this.cost = p_cost;
    }

 
    @Override
    public
    final long getValue() {
        return cost;
    }
}
