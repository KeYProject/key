package org.key_project.jmlediting.profile.jmlref;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.profile.jmlref.behavior.BehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.behavior.ExceptionalBehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.behavior.NormalBehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.bound_mod.BoundVarModifierKeywordSort;
import org.key_project.jmlediting.profile.jmlref.bound_mod.NonNullBoundModKeyword;
import org.key_project.jmlediting.profile.jmlref.bound_mod.NullableBoundModKeyword;
import org.key_project.jmlediting.profile.jmlref.loop.DecreasingKeyword;
import org.key_project.jmlediting.profile.jmlref.loop.LoopInvariantKeyword;
import org.key_project.jmlediting.profile.jmlref.model.GhostKeyword;
import org.key_project.jmlediting.profile.jmlref.model.ModelKeyword;
import org.key_project.jmlediting.profile.jmlref.model.RepresentsKeyword;
import org.key_project.jmlediting.profile.jmlref.model.SetKeyword;
import org.key_project.jmlediting.profile.jmlref.model.SuchThatKeyword;
import org.key_project.jmlediting.profile.jmlref.other.AlsoKeyword;
import org.key_project.jmlediting.profile.jmlref.other.HelperKeyword;
import org.key_project.jmlediting.profile.jmlref.other.InvariantKeyword;
import org.key_project.jmlediting.profile.jmlref.other.NonNullKeyword;
import org.key_project.jmlediting.profile.jmlref.other.NullableKeyword;
import org.key_project.jmlediting.profile.jmlref.other.PureKeyword;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionArgParser;
import org.key_project.jmlediting.profile.jmlref.parser.PredicateContentParser;
import org.key_project.jmlediting.profile.jmlref.parser.PredicateOtNotSpecifiedParser;
import org.key_project.jmlediting.profile.jmlref.parser.SpecExpressionContentParser;
import org.key_project.jmlediting.profile.jmlref.parser.StoreRefKeywordContentParser;
import org.key_project.jmlediting.profile.jmlref.parser.TargetLabelPredOrNotParser;
import org.key_project.jmlediting.profile.jmlref.parser.TrinarySpecExpressionArgParser;
import org.key_project.jmlediting.profile.jmlref.parser.TypeArgParser;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;
import org.key_project.jmlediting.profile.jmlref.primary.FreshKeyword;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.primary.InvariantForKeyword;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.primary.KeywordJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.primary.ReachKeyword;
import org.key_project.jmlediting.profile.jmlref.primary.TypeKeyword;
import org.key_project.jmlediting.profile.jmlref.primary.TypeofKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.ExistentialQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.ForallQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.MaxQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.MinQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.NumOfQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.ProductQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierKeywordSort;
import org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierPrimary;
import org.key_project.jmlediting.profile.jmlref.quantifier.SumQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AxiomKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.DivergesKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.EnsuresKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.InitiallyKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.MeasuredByKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SignalsKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SignalsOnlyKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.requires.RequiresKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.requires.RequiresValueKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.requires.SameKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.OldKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ResultKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.EverythingKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NotSpecifiedKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NothingKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_statement.BreakClauseKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_statement.ContinuesClauseKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_statement.ReturnsClauseKeyword;
import org.key_project.jmlediting.profile.jmlref.type.BigIntKeyword;
import org.key_project.jmlediting.profile.jmlref.type.RealKeyword;
import org.key_project.jmlediting.profile.jmlref.type.TypeKeywordSort;
import org.key_project.jmlediting.profile.jmlref.visibility.FinalKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.InstanceKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.PrivateKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.ProtectedKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.PublicKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.SpecProtectedKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.SpecPublicKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.StaticKeyword;

/**
 * Models JML with respect to the JML reference manual.
 * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/.
 *
 *
 * @author Moritz Lichter
 *
 */
public class JMLReferenceProfile extends AbstractJMLProfile implements
IJMLExpressionProfile {

   /**
    * The set containing all supported keywords.
    */
   private final Set<IJMLPrimary> supportedPrimaries = new HashSet<IJMLPrimary>();

   /**
    * Creates a new profile instance with the given supported keyword.
    *
    * @param lang
    *           the keyword locale for AE/BE
    */
   public JMLReferenceProfile(final KeywordLocale lang) {
      this.getSupportedKeywordsInternal().addAll(
            Arrays.asList(new EnsuresKeyword(), new AssignableKeyword(),
                  new AccessibleKeyword(), new RequiresKeyword(),
                  new BehaviorKeyword(lang), new ExceptionalBehaviorKeyword(
                        lang), new NormalBehaviorKeyword(lang),
                        new AlsoKeyword(), new HelperKeyword(), new PureKeyword(),
                        new PrivateKeyword(), new ProtectedKeyword(),
                        new PublicKeyword(), new SpecProtectedKeyword(),
                        new SpecPublicKeyword(), new EverythingKeyword(),
                        new NothingKeyword(), new NotSpecifiedKeyword(),
                        new ResultKeyword(), new OldKeyword(), new SameKeyword(),
                        new ForallQuantifierKeyword(),
                        new ExistentialQuantifierKeyword(),
                        new MinQuantifierKeyword(), new MaxQuantifierKeyword(),
                        new ProductQuantifierKeyword(), new SumQuantifierKeyword(),
                        new NumOfQuantifierKeyword(), new NonNullBoundModKeyword(),
                        new NullableBoundModKeyword(), new InvariantKeyword(),
                        new LoopInvariantKeyword(), new DecreasingKeyword(),
                        new InvariantForKeyword(), new SuchThatKeyword(),
                        new SetKeyword(), new ModelKeyword(), new GhostKeyword(),
                        new RepresentsKeyword(), new NonNullKeyword(),
                        new NullableKeyword(), new RealKeyword(),
                        new BigIntKeyword(), new DivergesKeyword(),
                        new MeasuredByKeyword(), new SignalsKeyword(),
                        new SignalsOnlyKeyword(), new AxiomKeyword(),
                        new TypeofKeyword(), new TypeKeyword(), new FreshKeyword(),
                        new ReachKeyword(), new InstanceKeyword(),
                        new StaticKeyword(), new InitiallyKeyword(),
                        new ContinuesClauseKeyword(), new BreakClauseKeyword(),
                        new ReturnsClauseKeyword(), new FinalKeyword()));

      this.getSupportedPrimariesInternal().addAll(
            Arrays.asList(new KeywordJMLPrimary(), new QuantifierPrimary()));

      this.getSupportedContentDescriptionsInternal().addAll(
            Arrays.asList(new UnarySpecExpressionArgParser(),
                  new BinarySpecExpressionArgParser(),
                  new TrinarySpecExpressionArgParser(),
                  new PredicateContentParser(),
                  new PredicateOtNotSpecifiedParser(), new TypeArgParser(),
                  new StoreRefKeywordContentParser(true),
                  new StoreRefKeywordContentParser(false),
                  new SpecExpressionContentParser(),
                  new TargetLabelPredOrNotParser()));

      // Register supported sorts
      this.getAvailableKeywordSortsInternal().addAll(
            Arrays.asList(BoundVarModifierKeywordSort.INSTANCE,
                  JMLPrimaryKeywordSort.INSTANCE,
                  QuantifierKeywordSort.INSTANCE,
                  RequiresValueKeywordSort.INSTANCE,
                  StoreRefKeywordSort.INSTANCE, TypeKeywordSort.INSTANCE));

   }

   /**
    * Creates a {@link JMLReferenceProfile} without a restriction to American
    * oder British English.
    */
   public JMLReferenceProfile() {
      this(KeywordLocale.BOTH);
   }

   @Override
   public Set<IJMLPrimary> getSupportedPrimaries() {
      return Collections.unmodifiableSet(this.supportedPrimaries);
   }

   /**
    * Returns the modifiable version of the primaries set to allow subclasses to
    * access them.
    *
    * @return the modifiable primaries set
    */
   protected final Set<IJMLPrimary> getSupportedPrimariesInternal() {
      return this.supportedPrimaries;
   }

   @Override
   public String getName() {
      return "JML Reference";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.jmlref";
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

   @Override
   public IEditableDerivedProfile derive(final String id, final String name) {
      return new DerivedExpressionProfile(id, name, this);
   }

   @Override
   public Set<ParseFunction> getPrimarySuffixExtensions() {
      return Collections.emptySet();
   }
}
