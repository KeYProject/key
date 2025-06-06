/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

/// Restricts where a taclet may be applied. Any combination of these restrictions in possible.
public record ApplicationRestriction(int value) {
    public ApplicationRestriction {
        if ((value & ANTECEDENT_POLARITY) == ANTECEDENT_POLARITY
                && (value & SUCCEDENT_POLARITY) == SUCCEDENT_POLARITY) {
            throw new IllegalArgumentException(
                "Polarity cannot be antecedent and succedent at the same time");
        }
    }

    /// does not pose state restrictions on valid matchings
    public static final ApplicationRestriction NONE = new ApplicationRestriction(0);

    /// all taclet constituents must appear in the same state (and not below a modality (for
    /// efficiency reasons))
    public static final int SAME_UPDATE_LEVEL = 1;

    /// all taclet constituents must be in the same state as the sequent
    public static final int IN_SEQUENT_STATE = 2;

    /// If the surrounding formula has been decomposed completely, the find-term will NOT appear
    /// on
    /// the succedent. The formula `wellformed(h)` in `wellformed(h) ==>` or in
    /// `==> wellformed(h) ->(inv(h) = inv(h2))` or in `==> \if(b) \then(!wellformed(h))
    /// \else(!wellformed(h2))`
    /// has
    /// antecedent polarity. The formula `wellformed(h)` in
    /// `wellformed(h) <-> wellformed(h2) ==>`
    /// has NO antecedent polarity.
    ///
    /// If this flag is set, the rule matches **only** on positions with antecedent polarity.
    public static final int ANTECEDENT_POLARITY = 4;

    /// If the surrounding formula has been decomposed completely, the find-term will NOT appear
    /// on
    /// the antecedent. The formula `wellformed(h)` in `==> wellformed(h)` or in
    /// `wellformed(h) ->(inv(h) = inv(h2)) ==>` or in
    /// `\if(b) \then(!wellformed(h)) \else(!wellformed(h2)) ==>`
    /// has
    /// succedent polarity. The formula `wellformed(h)` in
    /// `wellformed(h) <-> wellformed(h2) ==>` has
    /// NO succedent polarity.
    ///
    /// If this flag is set, the rule matches **only** on positions with succedent polarity.
    public static final int SUCCEDENT_POLARITY = 8;

    /// @return `true` iff `this` and `o` have at least one common flag.
    public boolean matches(ApplicationRestriction o) {
        return (value() & o.value()) != 0;
    }

    /// @return `true` iff `this` and `value` have at least one common bit set to `1`.
    public boolean matches(int value) {
        return (value() & value) != 0;
    }

    /// @return a new restriction where all flags set by `this` or `restriction` are set.
    public ApplicationRestriction combine(ApplicationRestriction restriction) {
        return new ApplicationRestriction(this.value | restriction.value());
    }

    /// @return a new restriction where all flags set by `this` or `value` are set.
    public ApplicationRestriction combine(int value) {
        return new ApplicationRestriction(this.value | value);
    }

    @Override
    public String toString() {
        String res = "";
        if (matches(SAME_UPDATE_LEVEL)) {
            res += "\\sameUpdateLevel";
        }
        if (matches(IN_SEQUENT_STATE)) {
            res += "\\inSequentState";
        }
        if (matches(ANTECEDENT_POLARITY)) {
            res += "\\antecedentPolarity";
        }
        if (matches(SUCCEDENT_POLARITY)) {
            res += "\\succedentPolarity";
        }
        return res;
    }
}
