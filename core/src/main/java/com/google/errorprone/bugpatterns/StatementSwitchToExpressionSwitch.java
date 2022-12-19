/*
 * Copyright 2022 The Error Prone Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.errorprone.bugpatterns;

import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.collect.ImmutableSet.toImmutableSet;
import static com.google.common.collect.Iterables.getLast;
import static com.google.errorprone.BugPattern.SeverityLevel.WARNING;
import static com.google.errorprone.matchers.Description.NO_MATCH;
import static com.google.errorprone.util.ASTHelpers.getStartPosition;
import static com.google.errorprone.util.ASTHelpers.getSymbol;
import static com.google.errorprone.util.ASTHelpers.getType;
import static com.google.errorprone.util.ASTHelpers.isStatic;
import static com.google.errorprone.util.ASTHelpers.isSubtype;
import static com.sun.source.tree.Tree.Kind.BREAK;
import static com.sun.source.tree.Tree.Kind.EXPRESSION_STATEMENT;
import static com.sun.source.tree.Tree.Kind.RETURN;
import static com.sun.source.tree.Tree.Kind.THROW;
import static java.util.stream.Collectors.joining;

import com.google.auto.value.AutoValue;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import com.google.common.collect.Streams;
import com.google.errorprone.BugPattern;
import com.google.errorprone.ErrorProneFlags;
import com.google.errorprone.VisitorState;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.google.errorprone.bugpatterns.BugChecker.SwitchTreeMatcher;
import com.google.errorprone.fixes.SuggestedFix;
import com.google.errorprone.matchers.Description;
import com.google.errorprone.util.ASTHelpers;
import com.google.errorprone.util.Reachability;
import com.google.errorprone.util.RuntimeVersion;
import com.google.pipeline.flume.fj.FJ;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import java.io.BufferedReader;
import java.io.CharArrayReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import javax.lang.model.element.ElementKind;

/** Checks for statement switches that can be expressed as an equivalent expression switch. */
@BugPattern(
    severity = WARNING,
    summary = "This statement switch can be converted to an equivalent expression switch")
public final class StatementSwitchToExpressionSwitch extends BugChecker
    implements SwitchTreeMatcher {
  // Braces are not required if there is exactly one statement on the right hand of the arrow, and
  // it's either an ExpressionStatement or a Throw.  Refer to JLS 14 §14.11.1
  private static final ImmutableSet<Kind> KINDS_CONVERTIBLE_WITHOUT_BRACES =
      ImmutableSet.of(THROW, EXPRESSION_STATEMENT);

  private static final ImmutableSet<Kind> KINDS_RETURN_OR_THROW = ImmutableSet.of(THROW, RETURN);
  private static final Pattern FALL_THROUGH_PATTERN =
      Pattern.compile("\\bfalls?.?through\\b", Pattern.CASE_INSENSITIVE);
  // Tri-state to represent the fall-thru control flow of a particular case of a particular
  // statement switch
  private static enum CaseFallThru {
    DEFINITELY_DOES_NOT_FALL_THRU,
    MAYBE_FALLS_THRU,
    DEFINITELY_DOES_FALL_THRU
  };

  private final boolean enableDirectConversion;
  private final boolean enableReturnSwitchConversion;
  private final boolean enableAssignmentSwitchConversion;

  public StatementSwitchToExpressionSwitch(ErrorProneFlags flags) {
    this.enableDirectConversion =
        flags.getBoolean("StatementSwitchToExpressionSwitch:EnableDirectConversion").orElse(false);
    this.enableReturnSwitchConversion =
        flags
            .getBoolean("StatementSwitchToExpressionSwitch:EnableReturnSwitchConversion")
            .orElse(false);
    this.enableAssignmentSwitchConversion =
        flags
            .getBoolean("StatementSwitchToExpressionSwitch:EnableAssignmentSwitchConversion")
            .orElse(false);
  }

  @Override
  public Description matchSwitch(SwitchTree switchTree, VisitorState state) {
    // Expression switches finalized in Java 14
    if (!RuntimeVersion.isAtLeast14()) {
      // return NO_MATCH;
    }

    FJ.incrementCounter("matchSwitch");

    AnalysisResult analysisResult = analyzeSwitchTree(switchTree, state);

    System.out.println(
        "analysisResults: canConvertToReturn "
            + analysisResult.canConvertToReturnSwitch()
            + " canConvDirect "
            + analysisResult.canConvertDirectlyToExpressionSwitch()
            + " combinedWithNext: "
            + analysisResult.groupedWithNextCase());

    List<SuggestedFix> suggestedFixes = new ArrayList<>();
    if ((true || enableReturnSwitchConversion) && analysisResult.canConvertToReturnSwitch()) {
      suggestedFixes.add(convertToReturnSwitch(switchTree, state, analysisResult));
    }
    if (enableDirectConversion && analysisResult.canConvertDirectlyToExpressionSwitch()) {
      suggestedFixes.add(convertDirectlyToExpressionSwitch(switchTree, state, analysisResult));
    }

    if (enableAssignmentSwitchConversion && analysisResult.canConvertToAssignmentSwitch()) {
      // TODO
    }

    return suggestedFixes.isEmpty()
        ? NO_MATCH
        : buildDescription(switchTree).addAllFixes(suggestedFixes).build();
  }

  /*
  @Override
  public Description matchMethod(MethodTree tree, VisitorState state) {

    if (!enableAssignmentSwitchConversion) {
      return NO_MATCH;
    }

    //MethodSymbol methodSymbol = getSymbol(tree);
    //if (methodSymbol.isConstructor()) {


    buildTreeScanner(state).scan(tree.getBody(), null);
    return NO_MATCH;
  }*/

  /**
   * Analyzes a {@code SwitchTree}, and determines any possible findings and suggested fixes related
   * to expression switches that can be made. Does not report any findings or suggested fixes up to
   * the Error Prone framework.
   */
  private static AnalysisResult analyzeSwitchTree(SwitchTree switchTree, VisitorState state) {
    List<? extends CaseTree> cases = switchTree.getCases();
    // A given case is said to have definite control flow if we are sure it always or never falls
    // thru at the end of its statement block
    boolean allCasesHaveDefiniteControlFlow = true;
    // A case is said to be grouped with the next one if we are sure it can appear together with the
    // next case on the left hand side of the arrow when converted to an expression switch.  For
    // example "case A,B -> ..."
    List<Boolean> groupedWithNextCase = new ArrayList<>(Collections.nCopies(cases.size(), false));

    // Set of all enum values (names) explicitly listed in a case
    Set<String> handledEnumValues = new HashSet<>();
    // Does at least one case consist solely of returning a (non-void) expression?
    boolean hasSimpleReturnExpressionCase = false;
    // Does every case consist simply of a throw or returning a (non-void) expression?
    boolean allCasesAreSimpleReturnOrThrow = true;
    // Does at least one case consist of a simple assignment?
    boolean hasSimpleAssignmentExpressionCase = false;
    // Does every case consist simply of a throw or assignment?
    boolean allCasesAreSimpleAssignmentOrThrow = true;

    boolean hasDefaultCase = false;

    // One-pass scan to identify whether statement switch can be converted to expression switch and
    // return switch
    for (int caseIndex = 0; caseIndex < cases.size(); caseIndex++) {
      CaseTree caseTree = cases.get(caseIndex);
      System.out.println(
          String.format(
              "DEB case %d (coming in allCasesAreSimpleReturnOrThrow %b)  old is %s ",
              caseIndex,
              allCasesAreSimpleReturnOrThrow,
              caseTree.getExpression() == null
                  ? "null"
                  : state.getSourceForNode(caseTree.getExpression())));

      System.out.println(
          String.format(
              "DEB new is null? %b count %d caseTree %s ",
              getExpressions(caseTree) == null,
              getExpressions(caseTree).count(),
              caseTree.getExpression() == null
                  ? "null"
                  : state.getSourceForNode(caseTree.getExpression())));

      getExpressions(caseTree)
          .forEach(
              c -> {
                if (c != null) {
                  System.out.println(String.format("Case is %s", state.getSourceForNode(c)));
                } else {
                  System.out.println("Case is null");
                }
              });
      boolean isDefaultCase = (getExpressions(caseTree).count() == 0);
      hasDefaultCase |= isDefaultCase;
      // enum values included in a case statement
      handledEnumValues.addAll(
          getExpressions(caseTree)
              .filter(IdentifierTree.class::isInstance)
              .map(expressionTree -> ((IdentifierTree) expressionTree).getName().toString())
              .collect(toImmutableSet()));

      boolean isLastCaseInSwitch = caseIndex == cases.size() - 1;

      List<? extends StatementTree> statements = caseTree.getStatements();
      CaseFallThru caseFallThru = CaseFallThru.MAYBE_FALLS_THRU;
      if (statements.isEmpty()) {
        // If the code for this case is just an empty block, then it must fall thru
        caseFallThru = CaseFallThru.DEFINITELY_DOES_FALL_THRU;
        // Can group with the next case (unless this is the last case)
        boolean notLastCase = caseIndex < cases.size() - 1;
        groupedWithNextCase.set(caseIndex, notLastCase);
        allCasesAreSimpleReturnOrThrow &= notLastCase;
      } else {
        groupedWithNextCase.set(caseIndex, false);

        if (statements.size() == 1 && KINDS_RETURN_OR_THROW.contains(statements.get(0).getKind())) {
          System.out.println(
              String.format(
                  "Simple case block with return or throw. kind %s", statements.get(0).getKind()));
          // Is the case's statement block just the return of an expression?
          if (RETURN.equals(statements.get(0).getKind())) {
            System.out.println(
                String.format(
                    "Cast to return tree: %s ", state.getSourceForNode(statements.get(0))));
            Type returnType = ASTHelpers.getType(((ReturnTree) statements.get(0)).getExpression());
            System.out.println(String.format("Return type is %s", returnType));
            hasSimpleReturnExpressionCase |= (returnType != null);
          }
        } else {
          allCasesAreSimpleReturnOrThrow = false;
        }

        // Code for this case is non-empty
        if (areStatementsConvertibleToExpressionSwitch(statements, isLastCaseInSwitch)) {
          caseFallThru = CaseFallThru.DEFINITELY_DOES_NOT_FALL_THRU;
        }
      }

      if (isDefaultCase) {
        // The "default" case has distinct semantics; don't allow anything to fall into or out of
        // default case.  Exception: allowed to fall out of default case if it's the last case
        boolean fallsIntoDefaultCase = (caseIndex > 0) && groupedWithNextCase.get(caseIndex - 1);
        if (isLastCaseInSwitch) {
          allCasesHaveDefiniteControlFlow &= !fallsIntoDefaultCase;
        } else {
          allCasesHaveDefiniteControlFlow &=
              !fallsIntoDefaultCase
                  && CaseFallThru.DEFINITELY_DOES_NOT_FALL_THRU.equals(caseFallThru);
        }
      } else {
        // Cases other than default
        allCasesHaveDefiniteControlFlow &= !CaseFallThru.MAYBE_FALLS_THRU.equals(caseFallThru);
      }
      System.out.println(
          "CaseFallThru = "
              + caseFallThru
              + "  allCasesHaveDefiniteControlFlow "
              + allCasesHaveDefiniteControlFlow);
    }

    boolean canConvertToReturnSwitch =
        // All restrictions for direct conversion apply
        allCasesHaveDefiniteControlFlow
            // Each expression switch block must be a single throw or return
            && allCasesAreSimpleReturnOrThrow
            // At least one return is needed
            && hasSimpleReturnExpressionCase
            // The switch must be exhaustive
            && isSwitchExhaustive(
                hasDefaultCase, handledEnumValues, ASTHelpers.getType(switchTree.getExpression()));

    boolean canConvertToAssignmentSwitch =
        // All restrictions for direct conversion apply
        allCasesHaveDefiniteControlFlow
            // Each expression switch block must be a single throw or return
            && allCasesAreSimpleAssignmentOrThrow
            // At least one assignment is needed
            && hasSimpleAssignmentExpressionCase
            // The switch must be exhaustive (default case implies this)
            && hasDefaultCase;

    if (isSwitchExhaustive(
        hasDefaultCase, handledEnumValues, ASTHelpers.getType(switchTree.getExpression()))) {
      FJ.incrementCounter("matchSwitchIsExhaustive");
    }
    if (hasDefaultCase) {
      FJ.incrementCounter("matchHasDefaultCase");
    }
    if (allCasesAreSimpleReturnOrThrow) {
      FJ.incrementCounter("matchAllCasesAreSimpleReturnOrThrow");
    }
    if (hasSimpleReturnExpressionCase) {
      FJ.incrementCounter("matchHasSimpleReturnExpressionCase");
    }
    if (allCasesHaveDefiniteControlFlow) {
      FJ.incrementCounter("matchAllCasesHaveDefiniteControlFlow");
    }
    if (canConvertToReturnSwitch) {
      FJ.incrementCounter("matchCanConvertToReturnSwitch");
    } else {
      FJ.incrementCounter("matchCannotConvertToReturnSwitch");
    }
    if (canConvertToReturnSwitch && hasDefaultCase) {
      FJ.incrementCounter("matchCanConvertToReturnSwitchAndHasDefaultCase");
    }

    System.out.println(
        String.format(
            "canConvertToReturnSwitch %b. canConvertToAssignmentSwitch %b.  hasDef %b"
                + " allCasesHaveDefiniteControlFlow %b allCasesSimpleRetThrow %b"
                + " hasSimpleREturnExpression %b handledEnumValues %s hasSimpleReturnExCase %b",
            canConvertToReturnSwitch,
            canConvertToAssignmentSwitch,
            hasDefaultCase,
            allCasesHaveDefiniteControlFlow,
            allCasesAreSimpleReturnOrThrow,
            hasSimpleReturnExpressionCase,
            handledEnumValues,
            hasSimpleReturnExpressionCase));
    return AnalysisResult.of(
        /* canConvertDirectlyToExpressionSwitch= */ allCasesHaveDefiniteControlFlow,
        canConvertToReturnSwitch,
        canConvertToAssignmentSwitch,
        /* groupedWithNextCase= */ ImmutableList.copyOf(groupedWithNextCase));
  }

  /**
   * Ad-hoc algorithm to search for a surjective map from (non-null) values of the {@code switch}
   * expression to a {@code CaseTree}. This algorithm does not compute whether such a map exists,
   * but rather only whether it can find such a map.
   */
  private static boolean isSwitchExhaustive(
      boolean hasDefaultCase, Set<String> handledEnumValues, Type switchType) {
    if (hasDefaultCase) {
      // Anything not included in a case can be mapped to the default CaseTree
      return true;
    }

    // Handles switching on enum (map is bijective)
    if (switchType.asElement().getKind() != ElementKind.ENUM) {
      return false;
    }
    return Sets.difference(ASTHelpers.enumValues(switchType.asElement()), handledEnumValues)
        .isEmpty();
  }

  /**
   * Determines whether the supplied case's {@code statements} are capable of being mapped to an
   * equivalent expression switch case (without repeating code), returning {@code true} if so.
   * Detection is based on an ad-hoc algorithm that is not guaranteed to detect every convertible
   * instance (whether a given block can fall-thru is an undecidable proposition in general).
   */
  private static boolean areStatementsConvertibleToExpressionSwitch(
      List<? extends StatementTree> statements, boolean isLastCaseInSwitch) {
    // For the last case, we can always convert (fall through has no effect)
    if (isLastCaseInSwitch) {
      return true;
    }
    // Always falls-thru; can combine with next case (if present)
    if (statements.isEmpty()) {
      return true;
    }
    // We only look at whether the block can fall-thru; javac would have already reported an
    // error if the last statement in the block weren't reachable (in the JLS sense).  Since we know
    // it is reachable, whether the block can complete normally is independent of any preceding
    // statements.  If the last statement cannot complete normally, then the block cannot, and thus
    // the block cannot fall-thru
    return !Reachability.canCompleteNormally(getLast(statements));
  }

  /**
   * Transforms the supplied statement switch into an expression switch directly. In this
   * conversion, each nontrivial statement block is mapped one-to-one to a new {@code Expression} or
   * {@code StatementBlock} on the right-hand side. Comments are presevered wherever possible.
   */
  private SuggestedFix convertDirectlyToExpressionSwitch(
      SwitchTree switchTree, VisitorState state, AnalysisResult analysisResult) {

    List<? extends CaseTree> cases = switchTree.getCases();
    StringBuilder replacementCodeBuilder = new StringBuilder();
    replacementCodeBuilder
        .append("switch ")
        .append(state.getSourceForNode(switchTree.getExpression()))
        .append(" {");

    StringBuilder groupedCaseCommentsAccumulator = null;
    boolean firstCaseInGroup = true;
    for (int caseIndex = 0; caseIndex < cases.size(); caseIndex++) {
      CaseTree caseTree = cases.get(caseIndex);
      boolean isDefaultCase = caseTree.getExpression() == null;

      // For readability, filter out trailing unlabelled break statement because these become a
      // No-Op when used inside expression switches
      ImmutableList<StatementTree> filteredStatements = filterOutRedundantBreak(caseTree);
      String transformedBlockSource =
          transformBlock(caseTree, state, cases, caseIndex, filteredStatements);

      if (firstCaseInGroup) {
        groupedCaseCommentsAccumulator = new StringBuilder();
        replacementCodeBuilder.append("\n  ");
        if (!isDefaultCase) {
          replacementCodeBuilder.append("case ");
        }
      }
      replacementCodeBuilder.append(
          isDefaultCase ? "default" : printCaseExpressions(caseTree, state));

      if (analysisResult.groupedWithNextCase().get(caseIndex)) {
        firstCaseInGroup = false;
        replacementCodeBuilder.append(", ");
        // Capture comments from this case so they can be added to the group's transformed case
        if (!transformedBlockSource.trim().isEmpty()) {
          groupedCaseCommentsAccumulator.append(removeFallThruLines(transformedBlockSource));
        }
        // Add additional cases to the list on the lhs of the arrow
        continue;
      } else {
        // This case is the last case in its group, so insert the collected comments from the lhs of
        // the colon here
        transformedBlockSource = groupedCaseCommentsAccumulator + transformedBlockSource;
      }

      replacementCodeBuilder.append(" -> ");

      if (filteredStatements.isEmpty()) {
        // Transformed block has no code
        String trimmedTransformedBlockSource = transformedBlockSource.trim();
        // If block is just space or a single "break;" with no explanatory comments, then remove
        // it to eliminate redundancy and improve readability
        if (trimmedTransformedBlockSource.isEmpty()
            || "break;".equals(trimmedTransformedBlockSource)) {
          replacementCodeBuilder.append("{}");
        } else {
          replacementCodeBuilder.append("{").append(transformedBlockSource).append("\n}");
        }
      } else {
        // Transformed block has code
        // Extract comments (if any) for break that was removed as redundant
        Optional<String> commentsBeforeRemovedBreak =
            extractCommentsBeforeRemovedBreak(caseTree, state, filteredStatements);
        if (commentsBeforeRemovedBreak.isPresent()) {
          transformedBlockSource = transformedBlockSource + "\n" + commentsBeforeRemovedBreak.get();
        }

        // To improve readability, don't use braces on the rhs if not needed
        if (shouldTransformCaseWithoutBraces(
            filteredStatements, transformedBlockSource, filteredStatements.get(0), state)) {
          // Single statement with no comments - no braces needed
          replacementCodeBuilder.append(transformedBlockSource);
        } else {
          // Use braces on the rhs
          replacementCodeBuilder.append("{").append(transformedBlockSource).append("\n}");
        }
      }

      firstCaseInGroup = true;
    } // case loop

    // Close the switch statement
    replacementCodeBuilder.append("\n}");

    SuggestedFix.Builder suggestedFixBuilder =
        SuggestedFix.builder().replace(switchTree, replacementCodeBuilder.toString());

    return suggestedFixBuilder.build();
  }

  private SuggestedFix convertToReturnSwitch(
      SwitchTree switchTree, VisitorState state, AnalysisResult analysisResult) {

    List<? extends CaseTree> cases = switchTree.getCases();
    StringBuilder replacementCodeBuilder = new StringBuilder();
    replacementCodeBuilder
        .append("return switch ")
        .append(state.getSourceForNode(switchTree.getExpression()))
        .append(" {");

    StringBuilder groupedCaseCommentsAccumulator = null;
    boolean firstCaseInGroup = true;
    for (int caseIndex = 0; caseIndex < cases.size(); caseIndex++) {
      CaseTree caseTree = cases.get(caseIndex);
      boolean isDefaultCase = caseTree.getExpression() == null;

      String transformedBlockSource =
          transformReturnOrThrowBlock(caseTree, state, cases, caseIndex, caseTree.getStatements());

      if (firstCaseInGroup) {
        groupedCaseCommentsAccumulator = new StringBuilder();
        replacementCodeBuilder.append("\n  ");
        if (!isDefaultCase) {
          replacementCodeBuilder.append("case ");
        }
      }
      replacementCodeBuilder.append(
          isDefaultCase ? "default" : printCaseExpressions(caseTree, state));

      if (analysisResult.groupedWithNextCase().get(caseIndex)) {
        firstCaseInGroup = false;
        replacementCodeBuilder.append(", ");
        // Capture comments from this case so they can be added to the group's transformed case
        if (!transformedBlockSource.trim().isEmpty()) {
          groupedCaseCommentsAccumulator.append(removeFallThruLines(transformedBlockSource));
        }
        // Add additional cases to the list on the lhs of the arrow
        continue;
      } else {
        // This case is the last case in its group, so insert the collected comments from the lhs of
        // the colon here
        transformedBlockSource = groupedCaseCommentsAccumulator + transformedBlockSource;
      }

      replacementCodeBuilder.append(" -> ");

      // Single statement with no comments - no braces needed
      replacementCodeBuilder.append(transformedBlockSource);

      firstCaseInGroup = true;
    } // case loop

    // Close the switch statement
    replacementCodeBuilder.append("\n};");

    System.out.println(
        String.format(
            "Synth: %s which will replace %s",
            replacementCodeBuilder, state.getSourceForNode(switchTree)));

    SuggestedFix.Builder suggestedFixBuilder =
        SuggestedFix.builder().replace(switchTree, replacementCodeBuilder.toString());
    return suggestedFixBuilder.build();
  }

  /**
   * Extracts comments after the last filtered statement but before a removed trailing break
   * statement, if present.
   */
  private static Optional<String> extractCommentsBeforeRemovedBreak(
      CaseTree caseTree, VisitorState state, ImmutableList<StatementTree> filteredStatements) {

    // Was a trailing break removed and some expressions remain?
    if (caseTree.getStatements().size() > filteredStatements.size()
        && !filteredStatements.isEmpty()) {
      // Extract any comments after what is now the last statement and before the removed
      // break
      String commentsAfterNewLastStatement =
          state
              .getSourceCode()
              .subSequence(
                  state.getEndPosition(Iterables.getLast(filteredStatements)),
                  getStartPosition(
                      caseTree.getStatements().get(caseTree.getStatements().size() - 1)))
              .toString()
              .trim();
      if (!commentsAfterNewLastStatement.isEmpty()) {
        return Optional.of(commentsAfterNewLastStatement);
      }
    }
    return Optional.empty();
  }

  /**
   * If the block for this {@code CaseTree} ends with a {@code break} statement that would be
   * redundant after transformation, then filter out the relevant {@code break} statement.
   */
  private static ImmutableList<StatementTree> filterOutRedundantBreak(CaseTree caseTree) {
    boolean caseEndsWithUnlabelledBreak =
        Streams.findLast(caseTree.getStatements().stream())
            .filter(statement -> BREAK.equals(statement.getKind()))
            .filter(breakTree -> ((BreakTree) breakTree).getLabel() == null)
            .isPresent();
    return caseEndsWithUnlabelledBreak
        ? caseTree.getStatements().stream()
            .limit(caseTree.getStatements().size() - 1)
            .collect(toImmutableList())
        : ImmutableList.copyOf(caseTree.getStatements());
  }

  /** Transforms code for this case into the code under an expression switch. */
  private static String transformBlock(
      CaseTree caseTree,
      VisitorState state,
      List<? extends CaseTree> cases,
      int caseIndex,
      ImmutableList<StatementTree> filteredStatements) {

    StringBuilder transformedBlockBuilder = new StringBuilder();
    int codeBlockStart = extractLhsComments(caseTree, state, transformedBlockBuilder);
    int codeBlockEnd =
        filteredStatements.isEmpty()
            ? getBlockEnd(state, caseTree, cases, caseIndex)
            : state.getEndPosition(Streams.findLast(filteredStatements.stream()).get());
    transformedBlockBuilder.append(state.getSourceCode(), codeBlockStart, codeBlockEnd);

    return transformedBlockBuilder.toString();
  }

  private static String transformReturnOrThrowBlock(
      CaseTree caseTree,
      VisitorState state,
      List<? extends CaseTree> cases,
      int caseIndex,
      List<? extends StatementTree> statements) {

    StringBuilder transformedBlockBuilder = new StringBuilder();
    int codeBlockStart;
    int codeBlockEnd =
        statements.isEmpty()
            ? getBlockEnd(state, caseTree, cases, caseIndex)
            : state.getEndPosition(Streams.findLast(statements.stream()).get());

    if (statements.size() == 1 && statements.get(0).getKind().equals(RETURN)) {
      // For "return x;", we want to take source starting after the "return"
      extractLhsComments(caseTree, state, transformedBlockBuilder);
      ReturnTree returnTree = (ReturnTree) statements.get(0);
      codeBlockStart = getStartPosition(returnTree.getExpression());
      // TODO : what about comments after the return but before the expression ???
    } else {
      codeBlockStart = extractLhsComments(caseTree, state, transformedBlockBuilder);
    }
    transformedBlockBuilder.append(state.getSourceCode(), codeBlockStart, codeBlockEnd);

    return transformedBlockBuilder.toString();
  }

  /**
   * Extracts comments to the left side of the colon for the provided {@code CaseTree} into the
   * {@code StringBuilder}. Note that any whitespace between distinct comments is not necessarily
   * preserved exactly.
   */
  @CanIgnoreReturnValue
  private static int extractLhsComments(
      CaseTree caseTree, VisitorState state, StringBuilder stringBuilder) {

    int lhsStart = getStartPosition(caseTree);
    int lhsEnd =
        caseTree.getStatements().isEmpty()
            ? state.getEndPosition(caseTree)
            : getStartPosition(caseTree.getStatements().get(0));

    // Accumulate comments into transformed block
    state.getOffsetTokens(lhsStart, lhsEnd).stream()
        .flatMap(errorProneToken -> errorProneToken.comments().stream())
        .forEach(comment -> stringBuilder.append(comment.getText()).append("\n"));

    return lhsEnd;
  }

  /**
   * Finds the position in source corresponding to the end of the code block of the supplied {@code
   * caseIndex} within all {@code cases}.
   */
  private static int getBlockEnd(
      VisitorState state, CaseTree caseTree, List<? extends CaseTree> cases, int caseIndex) {

    if (caseIndex == cases.size() - 1) {
      return state.getEndPosition(caseTree);
    }

    return ((JCTree) cases.get(caseIndex + 1)).getStartPosition();
  }

  /**
   * Determines whether the supplied {@code case}'s logic should be expressed on the right of the
   * arrow symbol without braces, incorporating both language and readabilitiy considerations.
   */
  private static boolean shouldTransformCaseWithoutBraces(
      ImmutableList<StatementTree> statementTrees,
      String transformedBlockSource,
      StatementTree firstStatement,
      VisitorState state) {

    if (statementTrees.isEmpty()) {
      // Instead, express as "-> {}"
      return false;
    }

    if (statementTrees.size() > 1) {
      // Instead, express as a code block "-> { ... }"
      return false;
    }

    // If code has comments, use braces for readability
    if (!transformedBlockSource.trim().equals(state.getSourceForNode(firstStatement).trim())) {
      return false;
    }

    StatementTree onlyStatementTree = statementTrees.get(0);
    return KINDS_CONVERTIBLE_WITHOUT_BRACES.contains(onlyStatementTree.getKind());
  }

  /**
   * Removes any comment lines containing language similar to "fall thru". Intermediate line
   * delimiters are also changed to newline.
   */
  private static String removeFallThruLines(String comments) {
    StringBuilder output = new StringBuilder();
    try (BufferedReader br = new BufferedReader(new CharArrayReader(comments.toCharArray()))) {
      String line;
      while ((line = br.readLine()) != null) {
        if (!FALL_THROUGH_PATTERN.matcher(line).find()) {
          output.append(line).append("\n");
        }
      }
      // Remove trailing \n, if present
      return output.length() > 0 ? output.substring(0, output.length() - 1) : "";
    } catch (IOException e) {
      return comments;
    }
  }

  /** Prints source for all expressions in a given {@code case}, separated by commas. */
  private static String printCaseExpressions(CaseTree caseTree, VisitorState state) {
    return getExpressions(caseTree).map(state::getSourceForNode).collect(joining(", "));
  }

  @SuppressWarnings("unchecked")
  private static Stream<? extends ExpressionTree> getExpressions(CaseTree caseTree) {
    try {
      if (RuntimeVersion.isAtLeast12()) {
        return ((List<? extends ExpressionTree>)
                CaseTree.class.getMethod("getExpressions").invoke(caseTree))
            .stream();
      } else {
        // Conform to behavior of newer getExpressions API
        return caseTree.getExpression() == null
            ? Stream.empty()
            : Stream.of(caseTree.getExpression());
      }
    } catch (ReflectiveOperationException e) {
      throw new LinkageError(e.getMessage(), e);
    }
  }

  @AutoValue
  abstract static class AnalysisResult {
    abstract boolean canConvertDirectlyToExpressionSwitch();

    abstract boolean canConvertToReturnSwitch();

    abstract boolean canConvertToAssignmentSwitch();

    abstract ImmutableList<Boolean> groupedWithNextCase();

    static AnalysisResult of(
        boolean canConvertDirectlyToExpressionSwitch,
        boolean canConvertToReturnSwitch,
        boolean canConvertToAssignmentSwitch,
        ImmutableList<Boolean> groupedWithNextCase) {
      return new AutoValue_StatementSwitchToExpressionSwitch_AnalysisResult(
          canConvertDirectlyToExpressionSwitch,
          canConvertToReturnSwitch,
          canConvertToAssignmentSwitch,
          groupedWithNextCase);
    }
  }

  /////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////
  /////// enableAssignmentSwitchConversion
  //////////////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////

  private final TreeScanner<Void, Void> buildTreeScanner(VisitorState state) {

    Type throwableType = state.getSymtab().throwableType;

    return new TreeScanner<Void, Void>() {
      @Override
      public Void visitClass(ClassTree classTree, Void unused) {
        return null;
      }

      @Override
      public Void visitMethod(MethodTree methodTree, Void unused) {
        return null;
      }

      @Override
      public Void visitSwitch(SwitchTree methodTree, Void unused) {
        return null;
      }

      @Override
      public Void visitAssignment(AssignmentTree assignmentTree, Void unused) {
        Symbol variableSymbol = getSymbol(assignmentTree.getVariable());
        Type variableType = getType(assignmentTree.getVariable());
        System.out.println("XYZ found assignment of " + variableSymbol);
        if (variableSymbol != null
            && isStatic(variableSymbol)
            && isSubtype(variableType, throwableType, state)) {
          state.reportMatch(describeMatch(assignmentTree));
        }
        return super.visitAssignment(assignmentTree, null);
      }
    };
  }
}
