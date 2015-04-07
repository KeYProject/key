package org.key_project.jmlediting.profile.key;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import org.key_project.jmlediting.profile.jmlref.KeywordLocale;
import org.key_project.jmlediting.profile.jmlref.loop.DecreasingKeyword;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.primary.ReachKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.MeasuredByKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_statement.BreakClauseKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_statement.ContinuesClauseKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_statement.ReturnsClauseKeyword;
import org.key_project.jmlediting.profile.key.behavior.BreakBehaviorKeyword;
import org.key_project.jmlediting.profile.key.behavior.ContinueBehaviorKeyword;
import org.key_project.jmlediting.profile.key.behavior.ReturnBehaviorKeyword;
import org.key_project.jmlediting.profile.key.bounded_quantifier.BProdQuantifierKeyword;
import org.key_project.jmlediting.profile.key.bounded_quantifier.BSumQuantifierKeyword;
import org.key_project.jmlediting.profile.key.bounded_quantifier.BoundedQuantifierPrimary;
import org.key_project.jmlediting.profile.key.locset.AllFieldsKeyword;
import org.key_project.jmlediting.profile.key.locset.DisjointKeyword;
import org.key_project.jmlediting.profile.key.locset.EmptyKeywod;
import org.key_project.jmlediting.profile.key.locset.InfiniteUnionKeyword;
import org.key_project.jmlediting.profile.key.locset.IntersetOperatorKeyword;
import org.key_project.jmlediting.profile.key.locset.LocSetEverythingKeyword;
import org.key_project.jmlediting.profile.key.locset.LocSetKeyword;
import org.key_project.jmlediting.profile.key.locset.LocSetSuffix;
import org.key_project.jmlediting.profile.key.locset.ReachLocsKeyword;
import org.key_project.jmlediting.profile.key.locset.SetMinusOperatorKeyword;
import org.key_project.jmlediting.profile.key.locset.SetTypeKeyword;
import org.key_project.jmlediting.profile.key.locset.SetUnionOperatorKeyword;
import org.key_project.jmlediting.profile.key.locset.SubsetKeyword;
import org.key_project.jmlediting.profile.key.other.AccessibleMeasuredByKeyword;
import org.key_project.jmlediting.profile.key.other.DynamicLogicPrimary;
import org.key_project.jmlediting.profile.key.other.InvKeyword;
import org.key_project.jmlediting.profile.key.other.KeYAccessibleKeyword;
import org.key_project.jmlediting.profile.key.other.KeYAssignableKeyword;
import org.key_project.jmlediting.profile.key.other.KeYDecreasingKeyword;
import org.key_project.jmlediting.profile.key.other.KeYMeasuredByKeyword;
import org.key_project.jmlediting.profile.key.other.KeYReachKeyword;
import org.key_project.jmlediting.profile.key.other.LessThanNothingKeyword;
import org.key_project.jmlediting.profile.key.other.StrictlyNothingKeyword;
import org.key_project.jmlediting.profile.key.other.StrictlyPureKeyword;
import org.key_project.jmlediting.profile.key.parser.KeYTargetLabelPredicateParser;
import org.key_project.jmlediting.profile.key.primary.NewElemsFreshKeyword;
import org.key_project.jmlediting.profile.key.primary.NonNullElementsKeyword;
import org.key_project.jmlediting.profile.key.seq.ContainsKeyword;
import org.key_project.jmlediting.profile.key.seq.IndexKeyword;
import org.key_project.jmlediting.profile.key.seq.IndexOfKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqConcatKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqDefKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqEmptyKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqLengthKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqPrimary;
import org.key_project.jmlediting.profile.key.seq.SeqPrimaryParser;
import org.key_project.jmlediting.profile.key.seq.SeqPrimitiveKeywordSort;
import org.key_project.jmlediting.profile.key.seq.SeqPutKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqReverseKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqSingletonKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqSubKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqTypeKeyword;
import org.key_project.jmlediting.profile.key.seq.SingletonKeyword;
import org.key_project.jmlediting.profile.key.seq.ValuesKeyword;
import org.key_project.jmlediting.profile.key.spec_statement.KeYBreaksClauseKeyword;
import org.key_project.jmlediting.profile.key.spec_statement.KeYContinuesClauseKeyword;
import org.key_project.jmlediting.profile.key.spec_statement.KeYReturnsClauseKeyword;

public class KeYProfile extends JMLReferenceProfile {

   private final Set<ParseFunction> additionalPrimarySuffixes;

   public KeYProfile() {
      super(KeywordLocale.AMERICAN);

      final Set<IKeyword> supportedKeywords = this
            .getSupportedKeywordsInternal();
      final Set<IJMLPrimary> supportedPrimaries = this
            .getSupportedPrimariesInternal();
      this.additionalPrimarySuffixes = new HashSet<ParseFunction>(
            super.getPrimarySuffixExtensions());

      // Add strictly keywords
      supportedKeywords.add(new StrictlyPureKeyword());
      supportedKeywords.add(new StrictlyNothingKeyword());
      // Disable informal descriptions in Assignable/Accessible keywords
      replace(supportedKeywords, AssignableKeyword.class,
            new KeYAssignableKeyword());
      replace(supportedKeywords, AccessibleKeyword.class,
            new KeYAccessibleKeyword());
      supportedKeywords.addAll(Arrays.asList(new AccessibleMeasuredByKeyword(),
            new LessThanNothingKeyword()));

      replace(supportedKeywords, MeasuredByKeyword.class,
            new KeYMeasuredByKeyword());
      replace(supportedKeywords, ReachKeyword.class, new KeYReachKeyword());
      replace(supportedKeywords, DecreasingKeyword.class,
            new KeYDecreasingKeyword());

      // Key specific behaviors
      supportedKeywords.addAll(Arrays.asList(new BreakBehaviorKeyword(),
            new ContinueBehaviorKeyword(), new ReturnBehaviorKeyword()));

      supportedKeywords.add(new InvKeyword());
      supportedPrimaries.add(new DynamicLogicPrimary());

      // Support for LocSetExpressions
      // Add everything for a different sort
      supportedKeywords.add(new LocSetEverythingKeyword());
      // All other keywords
      supportedKeywords.addAll(Arrays.asList(new EmptyKeywod(),
            new InfiniteUnionKeyword(), new IntersetOperatorKeyword(),
            new ReachLocsKeyword(), new SetMinusOperatorKeyword(),
            new SetUnionOperatorKeyword(), new LocSetKeyword(),
            new AllFieldsKeyword(), new DisjointKeyword(), new SubsetKeyword(),
            new SetTypeKeyword()));
      this.additionalPrimarySuffixes.add(LocSetSuffix.locSetSuffixes());

      // Allows \inv as access on a not toplevel object just as for x[3].\inv
      this.additionalPrimarySuffixes.add(InvKeyword.invSuffix(this));

      // Support for seq expression
      supportedKeywords.addAll(Arrays.asList(new SeqTypeKeyword(),
            new SeqConcatKeyword(), new SeqDefKeyword(), new SeqEmptyKeyword(),
            new SeqSingletonKeyword(), new ValuesKeyword(),
            new ContainsKeyword(), new IndexOfKeyword(), new SeqSubKeyword(),
            new SeqLengthKeyword(), new SingletonKeyword(), new IndexKeyword(),
            new SeqReverseKeyword(), new SeqPutKeyword()));
      supportedPrimaries.add(new SeqPrimary());
      this.additionalPrimarySuffixes.add(SeqPrimaryParser.seqSuffix(this));

      // Other keywords
      supportedKeywords.addAll(Arrays.asList(new NewElemsFreshKeyword(),
            new NonNullElementsKeyword(), new BSumQuantifierKeyword(),
            new BSumQuantifierKeyword(), new BProdQuantifierKeyword()));
      supportedPrimaries.add(new BoundedQuantifierPrimary());

      replace(supportedKeywords, BreakClauseKeyword.class,
            new KeYBreaksClauseKeyword());
      replace(supportedKeywords, ContinuesClauseKeyword.class,
            new KeYContinuesClauseKeyword());
      replace(supportedKeywords, ReturnsClauseKeyword.class,
            new KeYReturnsClauseKeyword());

      // Support for other keyword contents to the user
      final Set<IUserDefinedKeywordContentDescription> contents = this
            .getSupportedContentDescriptionsInternal();
      contents.add(new KeYTargetLabelPredicateParser());

      this.getAvailableKeywordSortsInternal().addAll(
            Arrays.asList(SeqPrimitiveKeywordSort.INSTANCE));
      this.getSupportedContentDescriptionsInternal().addAll(
            Arrays.asList(new KeYTargetLabelPredicateParser()));
   }

   private static void replace(final Set<IKeyword> keywords,
         final Class<? extends IKeyword> toReplace, final IKeyword keyword) {
      final Iterator<IKeyword> iter = keywords.iterator();
      while (iter.hasNext()) {
         final IKeyword k = iter.next();
         if (k.getClass().equals(toReplace)) {
            iter.remove();
            break;
         }
      }
      keywords.add(keyword);
   }

   @Override
   public String getName() {
      return "KeY Profile";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.key";
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

   @Override
   public Set<ParseFunction> getPrimarySuffixExtensions() {
      return Collections.unmodifiableSet(this.additionalPrimarySuffixes);
   }

}
