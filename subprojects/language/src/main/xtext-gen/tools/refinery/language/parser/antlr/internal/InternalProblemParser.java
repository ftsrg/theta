package tools.refinery.language.parser.antlr.internal;

import org.eclipse.xtext.*;
import org.eclipse.xtext.parser.*;
import org.eclipse.xtext.parser.impl.*;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.common.util.Enumerator;
import org.eclipse.xtext.parser.antlr.AbstractInternalAntlrParser;
import org.eclipse.xtext.parser.antlr.XtextTokenStream;
import org.eclipse.xtext.parser.antlr.XtextTokenStream.HiddenTokens;
import org.eclipse.xtext.parser.antlr.AntlrDatatypeRuleToken;
import tools.refinery.language.services.ProblemGrammarAccess;



import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
@SuppressWarnings("all")
public class InternalProblemParser extends AbstractInternalAntlrParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "Concretization", "Propagation", "Aggregator", "Candidate", "Container", "Primitive", "Abstract", "Contains", "Datatype", "Decision", "Opposite", "Declare", "Default", "Extends", "Partial", "Problem", "Subsets", "Unknown", "Assert", "Import", "Module", "Refers", "Shadow", "Class", "Error", "False", "Multi", "Scope", "Atom", "Enum", "Must", "Pred", "Rule", "True", "ExclamationMarkEqualsSignEqualsSign", "LessThanSignHyphenMinusGreaterThanSign", "EqualsSignEqualsSignEqualsSign", "EqualsSignEqualsSignGreaterThanSign", "May", "ExclamationMarkEqualsSign", "AmpersandAmpersand", "AsteriskAsterisk", "PlusSignEqualsSign", "HyphenMinusGreaterThanSign", "FullStopFullStop", "SolidusReverseSolidus", "ColonColon", "ColonGreaterThanSign", "LessThanSignColon", "LessThanSignEqualsSign", "EqualsSignEqualsSign", "GreaterThanSignEqualsSign", "ReverseSolidusSolidus", "CircumflexAccentCircumflexAccent", "As", "Is", "VerticalLineVerticalLine", "ExclamationMark", "NumberSign", "LeftParenthesis", "RightParenthesis", "Asterisk", "PlusSign", "Comma", "HyphenMinus", "FullStop", "Solidus", "Colon", "Semicolon", "LessThanSign", "EqualsSign", "GreaterThanSign", "QuestionMark", "CommercialAt", "LeftSquareBracket", "RightSquareBracket", "LeftCurlyBracket", "RightCurlyBracket", "RULE_TRANSITIVE_CLOSURE", "RULE_QUALIFIED_NAME_SEPARATOR", "RULE_ID", "RULE_INT", "RULE_EXPONENTIAL", "RULE_SL_COMMENT", "RULE_STRING", "RULE_QUOTED_ID", "RULE_ML_COMMENT", "RULE_WS", "RULE_ANY_OTHER"
    };
    public static final int Enum=33;
    public static final int Import=23;
    public static final int LessThanSignHyphenMinusGreaterThanSign=39;
    public static final int False=29;
    public static final int Must=34;
    public static final int LessThanSign=73;
    public static final int CircumflexAccentCircumflexAccent=57;
    public static final int Assert=22;
    public static final int LeftParenthesis=63;
    public static final int Unknown=21;
    public static final int Extends=17;
    public static final int ExclamationMark=61;
    public static final int ExclamationMarkEqualsSignEqualsSign=38;
    public static final int GreaterThanSign=75;
    public static final int RULE_ID=84;
    public static final int RULE_QUOTED_ID=89;
    public static final int ColonGreaterThanSign=51;
    public static final int Concretization=4;
    public static final int GreaterThanSignEqualsSign=55;
    public static final int ColonColon=50;
    public static final int EqualsSignEqualsSign=54;
    public static final int PlusSign=66;
    public static final int RULE_INT=85;
    public static final int Contains=11;
    public static final int RULE_ML_COMMENT=90;
    public static final int LeftSquareBracket=78;
    public static final int Rule=36;
    public static final int Module=24;
    public static final int Propagation=5;
    public static final int May=42;
    public static final int VerticalLineVerticalLine=60;
    public static final int Is=59;
    public static final int ReverseSolidusSolidus=56;
    public static final int Comma=67;
    public static final int As=58;
    public static final int HyphenMinus=68;
    public static final int LessThanSignEqualsSign=53;
    public static final int Solidus=70;
    public static final int RightCurlyBracket=81;
    public static final int FullStop=69;
    public static final int Abstract=10;
    public static final int Pred=35;
    public static final int Aggregator=6;
    public static final int Multi=30;
    public static final int Declare=15;
    public static final int Default=16;
    public static final int Decision=13;
    public static final int Atom=32;
    public static final int CommercialAt=77;
    public static final int Semicolon=72;
    public static final int EqualsSignEqualsSignGreaterThanSign=41;
    public static final int SolidusReverseSolidus=49;
    public static final int QuestionMark=76;
    public static final int ExclamationMarkEqualsSign=43;
    public static final int HyphenMinusGreaterThanSign=47;
    public static final int True=37;
    public static final int Datatype=12;
    public static final int Container=8;
    public static final int Partial=18;
    public static final int Subsets=20;
    public static final int FullStopFullStop=48;
    public static final int LessThanSignColon=52;
    public static final int RightSquareBracket=79;
    public static final int Candidate=7;
    public static final int Opposite=14;
    public static final int RULE_EXPONENTIAL=86;
    public static final int RightParenthesis=64;
    public static final int RULE_QUALIFIED_NAME_SEPARATOR=83;
    public static final int EqualsSignEqualsSignEqualsSign=40;
    public static final int NumberSign=62;
    public static final int AsteriskAsterisk=45;
    public static final int RULE_TRANSITIVE_CLOSURE=82;
    public static final int Problem=19;
    public static final int Class=27;
    public static final int Refers=25;
    public static final int Shadow=26;
    public static final int RULE_STRING=88;
    public static final int RULE_SL_COMMENT=87;
    public static final int EqualsSign=74;
    public static final int Primitive=9;
    public static final int AmpersandAmpersand=44;
    public static final int Colon=71;
    public static final int EOF=-1;
    public static final int Asterisk=65;
    public static final int PlusSignEqualsSign=46;
    public static final int RULE_WS=91;
    public static final int LeftCurlyBracket=80;
    public static final int Error=28;
    public static final int RULE_ANY_OTHER=92;
    public static final int Scope=31;

    // delegates
    // delegators


        public InternalProblemParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public InternalProblemParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return InternalProblemParser.tokenNames; }
    public String getGrammarFileName() { return "InternalProblemParser.g"; }



     	private ProblemGrammarAccess grammarAccess;

        public InternalProblemParser(TokenStream input, ProblemGrammarAccess grammarAccess) {
            this(input);
            this.grammarAccess = grammarAccess;
            registerRules(grammarAccess.getGrammar());
        }

        @Override
        protected String getFirstRuleName() {
        	return "Problem";
       	}

       	@Override
       	protected ProblemGrammarAccess getGrammarAccess() {
       		return grammarAccess;
       	}




    // $ANTLR start "entryRuleProblem"
    // InternalProblemParser.g:58:1: entryRuleProblem returns [EObject current=null] : iv_ruleProblem= ruleProblem EOF ;
    public final EObject entryRuleProblem() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleProblem = null;


        try {
            // InternalProblemParser.g:58:48: (iv_ruleProblem= ruleProblem EOF )
            // InternalProblemParser.g:59:2: iv_ruleProblem= ruleProblem EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getProblemRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleProblem=ruleProblem();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleProblem; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleProblem"


    // $ANTLR start "ruleProblem"
    // InternalProblemParser.g:65:1: ruleProblem returns [EObject current=null] : ( ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )? ( (lv_statements_3_0= ruleStatement ) )* ) ;
    public final EObject ruleProblem() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        Enumerator lv_kind_0_0 = null;

        AntlrDatatypeRuleToken lv_name_1_0 = null;

        EObject lv_statements_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:71:2: ( ( ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )? ( (lv_statements_3_0= ruleStatement ) )* ) )
            // InternalProblemParser.g:72:2: ( ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )? ( (lv_statements_3_0= ruleStatement ) )* )
            {
            // InternalProblemParser.g:72:2: ( ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )? ( (lv_statements_3_0= ruleStatement ) )* )
            // InternalProblemParser.g:73:3: ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )? ( (lv_statements_3_0= ruleStatement ) )*
            {
            // InternalProblemParser.g:73:3: ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )?
            int alt2=2;
            alt2 = dfa2.predict(input);
            switch (alt2) {
                case 1 :
                    // InternalProblemParser.g:74:4: ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop
                    {
                    // InternalProblemParser.g:74:4: ( (lv_kind_0_0= ruleModuleKind ) )
                    // InternalProblemParser.g:75:5: (lv_kind_0_0= ruleModuleKind )
                    {
                    // InternalProblemParser.g:75:5: (lv_kind_0_0= ruleModuleKind )
                    // InternalProblemParser.g:76:6: lv_kind_0_0= ruleModuleKind
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getProblemAccess().getKindModuleKindEnumRuleCall_0_0_0());
                      					
                    }
                    pushFollow(FOLLOW_3);
                    lv_kind_0_0=ruleModuleKind();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getProblemRule());
                      						}
                      						set(
                      							current,
                      							"kind",
                      							lv_kind_0_0,
                      							"tools.refinery.language.Problem.ModuleKind");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    // InternalProblemParser.g:93:4: ( (lv_name_1_0= ruleQualifiedName ) )?
                    int alt1=2;
                    int LA1_0 = input.LA(1);

                    if ( ((LA1_0>=Concretization && LA1_0<=Aggregator)||(LA1_0>=Container && LA1_0<=Primitive)||(LA1_0>=Contains && LA1_0<=Opposite)||(LA1_0>=Problem && LA1_0<=Subsets)||LA1_0==Assert||LA1_0==Module||LA1_0==Shadow||LA1_0==Multi||LA1_0==Atom||LA1_0==ColonColon||LA1_0==As||LA1_0==RULE_ID||LA1_0==RULE_QUOTED_ID) ) {
                        alt1=1;
                    }
                    switch (alt1) {
                        case 1 :
                            // InternalProblemParser.g:94:5: (lv_name_1_0= ruleQualifiedName )
                            {
                            // InternalProblemParser.g:94:5: (lv_name_1_0= ruleQualifiedName )
                            // InternalProblemParser.g:95:6: lv_name_1_0= ruleQualifiedName
                            {
                            if ( state.backtracking==0 ) {

                              						newCompositeNode(grammarAccess.getProblemAccess().getNameQualifiedNameParserRuleCall_0_1_0());
                              					
                            }
                            pushFollow(FOLLOW_4);
                            lv_name_1_0=ruleQualifiedName();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						if (current==null) {
                              							current = createModelElementForParent(grammarAccess.getProblemRule());
                              						}
                              						set(
                              							current,
                              							"name",
                              							lv_name_1_0,
                              							"tools.refinery.language.Problem.QualifiedName");
                              						afterParserOrEnumRuleCall();
                              					
                            }

                            }


                            }
                            break;

                    }

                    otherlv_2=(Token)match(input,FullStop,FOLLOW_5); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_2, grammarAccess.getProblemAccess().getFullStopKeyword_0_2());
                      			
                    }

                    }
                    break;

            }

            // InternalProblemParser.g:117:3: ( (lv_statements_3_0= ruleStatement ) )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>=Concretization && LA3_0<=Aggregator)||(LA3_0>=Container && LA3_0<=Default)||(LA3_0>=Problem && LA3_0<=Subsets)||(LA3_0>=Assert && LA3_0<=Module)||(LA3_0>=Shadow && LA3_0<=Error)||(LA3_0>=Multi && LA3_0<=Enum)||(LA3_0>=Pred && LA3_0<=Rule)||LA3_0==ColonColon||LA3_0==As||(LA3_0>=ExclamationMark && LA3_0<=NumberSign)||(LA3_0>=QuestionMark && LA3_0<=CommercialAt)||LA3_0==RULE_ID||LA3_0==RULE_QUOTED_ID) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // InternalProblemParser.g:118:4: (lv_statements_3_0= ruleStatement )
            	    {
            	    // InternalProblemParser.g:118:4: (lv_statements_3_0= ruleStatement )
            	    // InternalProblemParser.g:119:5: lv_statements_3_0= ruleStatement
            	    {
            	    if ( state.backtracking==0 ) {

            	      					newCompositeNode(grammarAccess.getProblemAccess().getStatementsStatementParserRuleCall_1_0());
            	      				
            	    }
            	    pushFollow(FOLLOW_5);
            	    lv_statements_3_0=ruleStatement();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      					if (current==null) {
            	      						current = createModelElementForParent(grammarAccess.getProblemRule());
            	      					}
            	      					add(
            	      						current,
            	      						"statements",
            	      						lv_statements_3_0,
            	      						"tools.refinery.language.Problem.Statement");
            	      					afterParserOrEnumRuleCall();
            	      				
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleProblem"


    // $ANTLR start "entryRuleStatement"
    // InternalProblemParser.g:140:1: entryRuleStatement returns [EObject current=null] : iv_ruleStatement= ruleStatement EOF ;
    public final EObject entryRuleStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStatement = null;


        try {
            // InternalProblemParser.g:140:50: (iv_ruleStatement= ruleStatement EOF )
            // InternalProblemParser.g:141:2: iv_ruleStatement= ruleStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleStatement=ruleStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStatement; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleStatement"


    // $ANTLR start "ruleStatement"
    // InternalProblemParser.g:147:1: ruleStatement returns [EObject current=null] : (this_ImportStatement_0= ruleImportStatement | this_Assertion_1= ruleAssertion | this_AnnotatedStatement_2= ruleAnnotatedStatement | this_ScopeDeclaration_3= ruleScopeDeclaration | this_TopLevelAnnotation_4= ruleTopLevelAnnotation ) ;
    public final EObject ruleStatement() throws RecognitionException {
        EObject current = null;

        EObject this_ImportStatement_0 = null;

        EObject this_Assertion_1 = null;

        EObject this_AnnotatedStatement_2 = null;

        EObject this_ScopeDeclaration_3 = null;

        EObject this_TopLevelAnnotation_4 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:153:2: ( (this_ImportStatement_0= ruleImportStatement | this_Assertion_1= ruleAssertion | this_AnnotatedStatement_2= ruleAnnotatedStatement | this_ScopeDeclaration_3= ruleScopeDeclaration | this_TopLevelAnnotation_4= ruleTopLevelAnnotation ) )
            // InternalProblemParser.g:154:2: (this_ImportStatement_0= ruleImportStatement | this_Assertion_1= ruleAssertion | this_AnnotatedStatement_2= ruleAnnotatedStatement | this_ScopeDeclaration_3= ruleScopeDeclaration | this_TopLevelAnnotation_4= ruleTopLevelAnnotation )
            {
            // InternalProblemParser.g:154:2: (this_ImportStatement_0= ruleImportStatement | this_Assertion_1= ruleAssertion | this_AnnotatedStatement_2= ruleAnnotatedStatement | this_ScopeDeclaration_3= ruleScopeDeclaration | this_TopLevelAnnotation_4= ruleTopLevelAnnotation )
            int alt4=5;
            alt4 = dfa4.predict(input);
            switch (alt4) {
                case 1 :
                    // InternalProblemParser.g:155:3: this_ImportStatement_0= ruleImportStatement
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getStatementAccess().getImportStatementParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_ImportStatement_0=ruleImportStatement();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_ImportStatement_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:164:3: this_Assertion_1= ruleAssertion
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getStatementAccess().getAssertionParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_Assertion_1=ruleAssertion();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_Assertion_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:173:3: this_AnnotatedStatement_2= ruleAnnotatedStatement
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getStatementAccess().getAnnotatedStatementParserRuleCall_2());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_AnnotatedStatement_2=ruleAnnotatedStatement();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_AnnotatedStatement_2;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:182:3: this_ScopeDeclaration_3= ruleScopeDeclaration
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getStatementAccess().getScopeDeclarationParserRuleCall_3());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_ScopeDeclaration_3=ruleScopeDeclaration();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_ScopeDeclaration_3;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:191:3: this_TopLevelAnnotation_4= ruleTopLevelAnnotation
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getStatementAccess().getTopLevelAnnotationParserRuleCall_4());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_TopLevelAnnotation_4=ruleTopLevelAnnotation();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_TopLevelAnnotation_4;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleStatement"


    // $ANTLR start "entryRuleAnnotatedStatement"
    // InternalProblemParser.g:203:1: entryRuleAnnotatedStatement returns [EObject current=null] : iv_ruleAnnotatedStatement= ruleAnnotatedStatement EOF ;
    public final EObject entryRuleAnnotatedStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAnnotatedStatement = null;


        try {
            // InternalProblemParser.g:203:59: (iv_ruleAnnotatedStatement= ruleAnnotatedStatement EOF )
            // InternalProblemParser.g:204:2: iv_ruleAnnotatedStatement= ruleAnnotatedStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAnnotatedStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAnnotatedStatement=ruleAnnotatedStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAnnotatedStatement; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAnnotatedStatement"


    // $ANTLR start "ruleAnnotatedStatement"
    // InternalProblemParser.g:210:1: ruleAnnotatedStatement returns [EObject current=null] : (this_AnnotationContainer_0= ruleAnnotationContainer ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) ) ) ;
    public final EObject ruleAnnotatedStatement() throws RecognitionException {
        EObject current = null;

        Token lv_abstract_2_0=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        Token otherlv_7=null;
        Token otherlv_9=null;
        Token otherlv_11=null;
        Token otherlv_12=null;
        Token otherlv_13=null;
        Token otherlv_15=null;
        Token otherlv_17=null;
        Token otherlv_19=null;
        Token otherlv_21=null;
        Token otherlv_22=null;
        Token otherlv_23=null;
        Token otherlv_24=null;
        Token otherlv_26=null;
        Token otherlv_27=null;
        Token otherlv_29=null;
        Token otherlv_31=null;
        Token otherlv_32=null;
        Token otherlv_34=null;
        Token otherlv_36=null;
        Token otherlv_37=null;
        Token lv_shadow_38_0=null;
        Token otherlv_40=null;
        Token otherlv_42=null;
        Token otherlv_44=null;
        Token otherlv_45=null;
        Token otherlv_49=null;
        Token otherlv_51=null;
        Token otherlv_53=null;
        Token otherlv_55=null;
        Token otherlv_56=null;
        Token otherlv_58=null;
        Token otherlv_60=null;
        Token otherlv_62=null;
        Token otherlv_64=null;
        Token lv_shadow_66_0=null;
        Token otherlv_69=null;
        Token otherlv_71=null;
        Token otherlv_73=null;
        Token otherlv_74=null;
        Token otherlv_76=null;
        Token otherlv_78=null;
        Token otherlv_81=null;
        Token otherlv_83=null;
        Token otherlv_85=null;
        Token otherlv_87=null;
        Token otherlv_88=null;
        Token otherlv_90=null;
        Token otherlv_92=null;
        Token otherlv_94=null;
        Token otherlv_96=null;
        Token otherlv_98=null;
        Token otherlv_99=null;
        Token otherlv_101=null;
        Token otherlv_103=null;
        Token otherlv_105=null;
        Token otherlv_106=null;
        Token otherlv_108=null;
        Token otherlv_109=null;
        Token otherlv_112=null;
        Token otherlv_114=null;
        EObject this_AnnotationContainer_0 = null;

        AntlrDatatypeRuleToken lv_name_4_0 = null;

        EObject lv_featureDeclarations_10_0 = null;

        AntlrDatatypeRuleToken lv_name_16_0 = null;

        EObject lv_literals_18_0 = null;

        EObject lv_literals_20_0 = null;

        AntlrDatatypeRuleToken lv_name_28_0 = null;

        AntlrDatatypeRuleToken lv_name_33_0 = null;

        AntlrDatatypeRuleToken lv_name_39_0 = null;

        EObject lv_parameters_41_0 = null;

        EObject lv_parameters_43_0 = null;

        Enumerator lv_kind_47_0 = null;

        Enumerator lv_kind_48_0 = null;

        AntlrDatatypeRuleToken lv_name_50_0 = null;

        EObject lv_parameters_52_0 = null;

        EObject lv_parameters_54_0 = null;

        EObject lv_bodies_61_0 = null;

        EObject lv_bodies_63_0 = null;

        AntlrDatatypeRuleToken lv_name_68_0 = null;

        EObject lv_parameters_70_0 = null;

        EObject lv_parameters_72_0 = null;

        EObject lv_cases_75_0 = null;

        EObject lv_cases_77_0 = null;

        Enumerator lv_kind_80_0 = null;

        AntlrDatatypeRuleToken lv_name_82_0 = null;

        EObject lv_parameters_84_0 = null;

        EObject lv_parameters_86_0 = null;

        EObject lv_preconditions_89_0 = null;

        EObject lv_preconditions_91_0 = null;

        EObject lv_consequents_93_0 = null;

        EObject lv_consequents_95_0 = null;

        AntlrDatatypeRuleToken lv_name_100_0 = null;

        EObject lv_parameters_102_0 = null;

        EObject lv_parameters_104_0 = null;

        Enumerator lv_kind_110_0 = null;

        EObject lv_nodes_111_0 = null;

        EObject lv_nodes_113_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:216:2: ( (this_AnnotationContainer_0= ruleAnnotationContainer ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) ) ) )
            // InternalProblemParser.g:217:2: (this_AnnotationContainer_0= ruleAnnotationContainer ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) ) )
            {
            // InternalProblemParser.g:217:2: (this_AnnotationContainer_0= ruleAnnotationContainer ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) ) )
            // InternalProblemParser.g:218:3: this_AnnotationContainer_0= ruleAnnotationContainer ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) )
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getAnnotationContainerParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_6);
            this_AnnotationContainer_0=ruleAnnotationContainer();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_AnnotationContainer_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:226:3: ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) )
            int alt43=10;
            alt43 = dfa43.predict(input);
            switch (alt43) {
                case 1 :
                    // InternalProblemParser.g:227:4: ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) )
                    {
                    // InternalProblemParser.g:227:4: ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) )
                    // InternalProblemParser.g:228:5: () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop )
                    {
                    // InternalProblemParser.g:228:5: ()
                    // InternalProblemParser.g:229:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getClassDeclarationAnnotationsAction_1_0_0(),
                      							current);
                      					
                    }

                    }

                    // InternalProblemParser.g:235:5: ( (lv_abstract_2_0= Abstract ) )?
                    int alt5=2;
                    int LA5_0 = input.LA(1);

                    if ( (LA5_0==Abstract) ) {
                        alt5=1;
                    }
                    switch (alt5) {
                        case 1 :
                            // InternalProblemParser.g:236:6: (lv_abstract_2_0= Abstract )
                            {
                            // InternalProblemParser.g:236:6: (lv_abstract_2_0= Abstract )
                            // InternalProblemParser.g:237:7: lv_abstract_2_0= Abstract
                            {
                            lv_abstract_2_0=(Token)match(input,Abstract,FOLLOW_7); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(lv_abstract_2_0, grammarAccess.getAnnotatedStatementAccess().getAbstractAbstractKeyword_1_0_1_0());
                              						
                            }
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                              							}
                              							setWithLastConsumed(current, "abstract", lv_abstract_2_0 != null, "abstract");
                              						
                            }

                            }


                            }
                            break;

                    }

                    otherlv_3=(Token)match(input,Class,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_3, grammarAccess.getAnnotatedStatementAccess().getClassKeyword_1_0_2());
                      				
                    }
                    // InternalProblemParser.g:253:5: ( (lv_name_4_0= ruleIdentifier ) )
                    // InternalProblemParser.g:254:6: (lv_name_4_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:254:6: (lv_name_4_0= ruleIdentifier )
                    // InternalProblemParser.g:255:7: lv_name_4_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_0_3_0());
                      						
                    }
                    pushFollow(FOLLOW_9);
                    lv_name_4_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_4_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:272:5: (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )?
                    int alt7=2;
                    int LA7_0 = input.LA(1);

                    if ( (LA7_0==Extends) ) {
                        alt7=1;
                    }
                    switch (alt7) {
                        case 1 :
                            // InternalProblemParser.g:273:6: otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )*
                            {
                            otherlv_5=(Token)match(input,Extends,FOLLOW_8); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_5, grammarAccess.getAnnotatedStatementAccess().getExtendsKeyword_1_0_4_0());
                              					
                            }
                            // InternalProblemParser.g:277:6: ( ( ruleQualifiedName ) )
                            // InternalProblemParser.g:278:7: ( ruleQualifiedName )
                            {
                            // InternalProblemParser.g:278:7: ( ruleQualifiedName )
                            // InternalProblemParser.g:279:8: ruleQualifiedName
                            {
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                              								}
                              							
                            }
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getSuperTypesRelationCrossReference_1_0_4_1_0());
                              							
                            }
                            pushFollow(FOLLOW_10);
                            ruleQualifiedName();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:293:6: (otherlv_7= Comma ( ( ruleQualifiedName ) ) )*
                            loop6:
                            do {
                                int alt6=2;
                                int LA6_0 = input.LA(1);

                                if ( (LA6_0==Comma) ) {
                                    alt6=1;
                                }


                                switch (alt6) {
                            	case 1 :
                            	    // InternalProblemParser.g:294:7: otherlv_7= Comma ( ( ruleQualifiedName ) )
                            	    {
                            	    otherlv_7=(Token)match(input,Comma,FOLLOW_8); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_7, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_0_4_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:298:7: ( ( ruleQualifiedName ) )
                            	    // InternalProblemParser.g:299:8: ( ruleQualifiedName )
                            	    {
                            	    // InternalProblemParser.g:299:8: ( ruleQualifiedName )
                            	    // InternalProblemParser.g:300:9: ruleQualifiedName
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      								
                            	    }
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getSuperTypesRelationCrossReference_1_0_4_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_10);
                            	    ruleQualifiedName();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop6;
                                }
                            } while (true);


                            }
                            break;

                    }

                    // InternalProblemParser.g:316:5: ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop )
                    int alt10=2;
                    int LA10_0 = input.LA(1);

                    if ( (LA10_0==LeftCurlyBracket) ) {
                        alt10=1;
                    }
                    else if ( (LA10_0==FullStop) ) {
                        alt10=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 10, 0, input);

                        throw nvae;
                    }
                    switch (alt10) {
                        case 1 :
                            // InternalProblemParser.g:317:6: (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket )
                            {
                            // InternalProblemParser.g:317:6: (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket )
                            // InternalProblemParser.g:318:7: otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket
                            {
                            otherlv_9=(Token)match(input,LeftCurlyBracket,FOLLOW_11); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(otherlv_9, grammarAccess.getAnnotatedStatementAccess().getLeftCurlyBracketKeyword_1_0_5_0_0());
                              						
                            }
                            // InternalProblemParser.g:322:7: ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )*
                            loop9:
                            do {
                                int alt9=2;
                                int LA9_0 = input.LA(1);

                                if ( (LA9_0==EOF||(LA9_0>=Concretization && LA9_0<=Aggregator)||(LA9_0>=Container && LA9_0<=Declare)||(LA9_0>=Problem && LA9_0<=Subsets)||LA9_0==Assert||(LA9_0>=Module && LA9_0<=Error)||LA9_0==Multi||(LA9_0>=Atom && LA9_0<=Enum)||(LA9_0>=Pred && LA9_0<=Rule)||LA9_0==ColonColon||LA9_0==As||LA9_0==NumberSign||LA9_0==CommercialAt||LA9_0==RULE_ID||LA9_0==RULE_QUOTED_ID) ) {
                                    alt9=1;
                                }


                                switch (alt9) {
                            	case 1 :
                            	    // InternalProblemParser.g:323:8: ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )?
                            	    {
                            	    // InternalProblemParser.g:323:8: ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) )
                            	    // InternalProblemParser.g:324:9: (lv_featureDeclarations_10_0= ruleReferenceDeclaration )
                            	    {
                            	    // InternalProblemParser.g:324:9: (lv_featureDeclarations_10_0= ruleReferenceDeclaration )
                            	    // InternalProblemParser.g:325:10: lv_featureDeclarations_10_0= ruleReferenceDeclaration
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      										newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getFeatureDeclarationsReferenceDeclarationParserRuleCall_1_0_5_0_1_0_0());
                            	      									
                            	    }
                            	    pushFollow(FOLLOW_12);
                            	    lv_featureDeclarations_10_0=ruleReferenceDeclaration();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      										if (current==null) {
                            	      											current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      										}
                            	      										add(
                            	      											current,
                            	      											"featureDeclarations",
                            	      											lv_featureDeclarations_10_0,
                            	      											"tools.refinery.language.Problem.ReferenceDeclaration");
                            	      										afterParserOrEnumRuleCall();
                            	      									
                            	    }

                            	    }


                            	    }

                            	    // InternalProblemParser.g:342:8: (otherlv_11= Semicolon )?
                            	    int alt8=2;
                            	    int LA8_0 = input.LA(1);

                            	    if ( (LA8_0==Semicolon) ) {
                            	        alt8=1;
                            	    }
                            	    switch (alt8) {
                            	        case 1 :
                            	            // InternalProblemParser.g:343:9: otherlv_11= Semicolon
                            	            {
                            	            otherlv_11=(Token)match(input,Semicolon,FOLLOW_11); if (state.failed) return current;
                            	            if ( state.backtracking==0 ) {

                            	              									newLeafNode(otherlv_11, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_0_5_0_1_1());
                            	              								
                            	            }

                            	            }
                            	            break;

                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop9;
                                }
                            } while (true);

                            otherlv_12=(Token)match(input,RightCurlyBracket,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(otherlv_12, grammarAccess.getAnnotatedStatementAccess().getRightCurlyBracketKeyword_1_0_5_0_2());
                              						
                            }

                            }


                            }
                            break;
                        case 2 :
                            // InternalProblemParser.g:355:6: otherlv_13= FullStop
                            {
                            otherlv_13=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_13, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_0_5_1());
                              					
                            }

                            }
                            break;

                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:362:4: ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) )
                    {
                    // InternalProblemParser.g:362:4: ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) )
                    // InternalProblemParser.g:363:5: () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop )
                    {
                    // InternalProblemParser.g:363:5: ()
                    // InternalProblemParser.g:364:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getEnumDeclarationAnnotationsAction_1_1_0(),
                      							current);
                      					
                    }

                    }

                    otherlv_15=(Token)match(input,Enum,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_15, grammarAccess.getAnnotatedStatementAccess().getEnumKeyword_1_1_1());
                      				
                    }
                    // InternalProblemParser.g:374:5: ( (lv_name_16_0= ruleIdentifier ) )
                    // InternalProblemParser.g:375:6: (lv_name_16_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:375:6: (lv_name_16_0= ruleIdentifier )
                    // InternalProblemParser.g:376:7: lv_name_16_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_1_2_0());
                      						
                    }
                    pushFollow(FOLLOW_13);
                    lv_name_16_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_16_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:393:5: ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop )
                    int alt14=2;
                    int LA14_0 = input.LA(1);

                    if ( (LA14_0==LeftCurlyBracket) ) {
                        alt14=1;
                    }
                    else if ( (LA14_0==FullStop) ) {
                        alt14=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 14, 0, input);

                        throw nvae;
                    }
                    switch (alt14) {
                        case 1 :
                            // InternalProblemParser.g:394:6: (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket )
                            {
                            // InternalProblemParser.g:394:6: (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket )
                            // InternalProblemParser.g:395:7: otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket
                            {
                            otherlv_17=(Token)match(input,LeftCurlyBracket,FOLLOW_14); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(otherlv_17, grammarAccess.getAnnotatedStatementAccess().getLeftCurlyBracketKeyword_1_1_3_0_0());
                              						
                            }
                            // InternalProblemParser.g:399:7: ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )?
                            int alt13=2;
                            int LA13_0 = input.LA(1);

                            if ( (LA13_0==EOF||(LA13_0>=Concretization && LA13_0<=Aggregator)||(LA13_0>=Container && LA13_0<=Declare)||(LA13_0>=Problem && LA13_0<=Subsets)||LA13_0==Assert||(LA13_0>=Module && LA13_0<=Error)||LA13_0==Multi||(LA13_0>=Atom && LA13_0<=Enum)||(LA13_0>=Pred && LA13_0<=Rule)||LA13_0==ColonColon||LA13_0==As||LA13_0==NumberSign||LA13_0==CommercialAt||LA13_0==RULE_ID||LA13_0==RULE_QUOTED_ID) ) {
                                alt13=1;
                            }
                            switch (alt13) {
                                case 1 :
                                    // InternalProblemParser.g:400:8: ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )?
                                    {
                                    // InternalProblemParser.g:400:8: ( (lv_literals_18_0= ruleEnumLiteral ) )
                                    // InternalProblemParser.g:401:9: (lv_literals_18_0= ruleEnumLiteral )
                                    {
                                    // InternalProblemParser.g:401:9: (lv_literals_18_0= ruleEnumLiteral )
                                    // InternalProblemParser.g:402:10: lv_literals_18_0= ruleEnumLiteral
                                    {
                                    if ( state.backtracking==0 ) {

                                      										newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getLiteralsEnumLiteralParserRuleCall_1_1_3_0_1_0_0());
                                      									
                                    }
                                    pushFollow(FOLLOW_15);
                                    lv_literals_18_0=ruleEnumLiteral();

                                    state._fsp--;
                                    if (state.failed) return current;
                                    if ( state.backtracking==0 ) {

                                      										if (current==null) {
                                      											current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                                      										}
                                      										add(
                                      											current,
                                      											"literals",
                                      											lv_literals_18_0,
                                      											"tools.refinery.language.Problem.EnumLiteral");
                                      										afterParserOrEnumRuleCall();
                                      									
                                    }

                                    }


                                    }

                                    // InternalProblemParser.g:419:8: (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )*
                                    loop11:
                                    do {
                                        int alt11=2;
                                        int LA11_0 = input.LA(1);

                                        if ( (LA11_0==Comma) ) {
                                            int LA11_1 = input.LA(2);

                                            if ( ((LA11_1>=Concretization && LA11_1<=Aggregator)||(LA11_1>=Container && LA11_1<=Primitive)||(LA11_1>=Contains && LA11_1<=Opposite)||(LA11_1>=Problem && LA11_1<=Subsets)||LA11_1==Assert||LA11_1==Module||LA11_1==Shadow||LA11_1==Multi||LA11_1==Atom||LA11_1==As||LA11_1==CommercialAt||LA11_1==RULE_ID||LA11_1==RULE_QUOTED_ID) ) {
                                                alt11=1;
                                            }


                                        }


                                        switch (alt11) {
                                    	case 1 :
                                    	    // InternalProblemParser.g:420:9: otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) )
                                    	    {
                                    	    otherlv_19=(Token)match(input,Comma,FOLLOW_16); if (state.failed) return current;
                                    	    if ( state.backtracking==0 ) {

                                    	      									newLeafNode(otherlv_19, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_1_3_0_1_1_0());
                                    	      								
                                    	    }
                                    	    // InternalProblemParser.g:424:9: ( (lv_literals_20_0= ruleEnumLiteral ) )
                                    	    // InternalProblemParser.g:425:10: (lv_literals_20_0= ruleEnumLiteral )
                                    	    {
                                    	    // InternalProblemParser.g:425:10: (lv_literals_20_0= ruleEnumLiteral )
                                    	    // InternalProblemParser.g:426:11: lv_literals_20_0= ruleEnumLiteral
                                    	    {
                                    	    if ( state.backtracking==0 ) {

                                    	      											newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getLiteralsEnumLiteralParserRuleCall_1_1_3_0_1_1_1_0());
                                    	      										
                                    	    }
                                    	    pushFollow(FOLLOW_15);
                                    	    lv_literals_20_0=ruleEnumLiteral();

                                    	    state._fsp--;
                                    	    if (state.failed) return current;
                                    	    if ( state.backtracking==0 ) {

                                    	      											if (current==null) {
                                    	      												current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                                    	      											}
                                    	      											add(
                                    	      												current,
                                    	      												"literals",
                                    	      												lv_literals_20_0,
                                    	      												"tools.refinery.language.Problem.EnumLiteral");
                                    	      											afterParserOrEnumRuleCall();
                                    	      										
                                    	    }

                                    	    }


                                    	    }


                                    	    }
                                    	    break;

                                    	default :
                                    	    break loop11;
                                        }
                                    } while (true);

                                    // InternalProblemParser.g:444:8: (otherlv_21= Comma | otherlv_22= Semicolon )?
                                    int alt12=3;
                                    int LA12_0 = input.LA(1);

                                    if ( (LA12_0==Comma) ) {
                                        alt12=1;
                                    }
                                    else if ( (LA12_0==Semicolon) ) {
                                        alt12=2;
                                    }
                                    switch (alt12) {
                                        case 1 :
                                            // InternalProblemParser.g:445:9: otherlv_21= Comma
                                            {
                                            otherlv_21=(Token)match(input,Comma,FOLLOW_17); if (state.failed) return current;
                                            if ( state.backtracking==0 ) {

                                              									newLeafNode(otherlv_21, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_1_3_0_1_2_0());
                                              								
                                            }

                                            }
                                            break;
                                        case 2 :
                                            // InternalProblemParser.g:450:9: otherlv_22= Semicolon
                                            {
                                            otherlv_22=(Token)match(input,Semicolon,FOLLOW_17); if (state.failed) return current;
                                            if ( state.backtracking==0 ) {

                                              									newLeafNode(otherlv_22, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_1_3_0_1_2_1());
                                              								
                                            }

                                            }
                                            break;

                                    }


                                    }
                                    break;

                            }

                            otherlv_23=(Token)match(input,RightCurlyBracket,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(otherlv_23, grammarAccess.getAnnotatedStatementAccess().getRightCurlyBracketKeyword_1_1_3_0_2());
                              						
                            }

                            }


                            }
                            break;
                        case 2 :
                            // InternalProblemParser.g:462:6: otherlv_24= FullStop
                            {
                            otherlv_24=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_24, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_1_3_1());
                              					
                            }

                            }
                            break;

                    }


                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:469:4: ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop )
                    {
                    // InternalProblemParser.g:469:4: ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop )
                    // InternalProblemParser.g:470:5: () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop
                    {
                    // InternalProblemParser.g:470:5: ()
                    // InternalProblemParser.g:471:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getDatatypeDeclarationAnnotationsAction_1_2_0(),
                      							current);
                      					
                    }

                    }

                    otherlv_26=(Token)match(input,NumberSign,FOLLOW_18); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_26, grammarAccess.getAnnotatedStatementAccess().getNumberSignKeyword_1_2_1());
                      				
                    }
                    otherlv_27=(Token)match(input,Datatype,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_27, grammarAccess.getAnnotatedStatementAccess().getDatatypeKeyword_1_2_2());
                      				
                    }
                    // InternalProblemParser.g:485:5: ( (lv_name_28_0= ruleIdentifier ) )
                    // InternalProblemParser.g:486:6: (lv_name_28_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:486:6: (lv_name_28_0= ruleIdentifier )
                    // InternalProblemParser.g:487:7: lv_name_28_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_2_3_0());
                      						
                    }
                    pushFollow(FOLLOW_4);
                    lv_name_28_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_28_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_29=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_29, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_2_4());
                      				
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:510:4: ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop )
                    {
                    // InternalProblemParser.g:510:4: ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop )
                    // InternalProblemParser.g:511:5: () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop
                    {
                    // InternalProblemParser.g:511:5: ()
                    // InternalProblemParser.g:512:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getAggregatorDeclarationAnnotationsAction_1_3_0(),
                      							current);
                      					
                    }

                    }

                    otherlv_31=(Token)match(input,NumberSign,FOLLOW_19); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_31, grammarAccess.getAnnotatedStatementAccess().getNumberSignKeyword_1_3_1());
                      				
                    }
                    otherlv_32=(Token)match(input,Aggregator,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_32, grammarAccess.getAnnotatedStatementAccess().getAggregatorKeyword_1_3_2());
                      				
                    }
                    // InternalProblemParser.g:526:5: ( (lv_name_33_0= ruleIdentifier ) )
                    // InternalProblemParser.g:527:6: (lv_name_33_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:527:6: (lv_name_33_0= ruleIdentifier )
                    // InternalProblemParser.g:528:7: lv_name_33_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_3_3_0());
                      						
                    }
                    pushFollow(FOLLOW_4);
                    lv_name_33_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_33_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_34=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_34, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_3_4());
                      				
                    }

                    }


                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:551:4: ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop )
                    {
                    // InternalProblemParser.g:551:4: ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop )
                    // InternalProblemParser.g:552:5: () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop
                    {
                    // InternalProblemParser.g:552:5: ()
                    // InternalProblemParser.g:553:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getOverloadedDeclarationAnnotationsAction_1_4_0(),
                      							current);
                      					
                    }

                    }

                    otherlv_36=(Token)match(input,NumberSign,FOLLOW_20); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_36, grammarAccess.getAnnotatedStatementAccess().getNumberSignKeyword_1_4_1());
                      				
                    }
                    otherlv_37=(Token)match(input,Primitive,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_37, grammarAccess.getAnnotatedStatementAccess().getPrimitiveKeyword_1_4_2());
                      				
                    }
                    // InternalProblemParser.g:567:5: ( (lv_shadow_38_0= Shadow ) )?
                    int alt15=2;
                    int LA15_0 = input.LA(1);

                    if ( (LA15_0==Shadow) ) {
                        int LA15_1 = input.LA(2);

                        if ( ((LA15_1>=Concretization && LA15_1<=Aggregator)||(LA15_1>=Container && LA15_1<=Primitive)||(LA15_1>=Contains && LA15_1<=Opposite)||(LA15_1>=Problem && LA15_1<=Subsets)||LA15_1==Assert||LA15_1==Module||LA15_1==Shadow||LA15_1==Multi||LA15_1==Atom||LA15_1==As||LA15_1==RULE_ID||LA15_1==RULE_QUOTED_ID) ) {
                            alt15=1;
                        }
                    }
                    switch (alt15) {
                        case 1 :
                            // InternalProblemParser.g:568:6: (lv_shadow_38_0= Shadow )
                            {
                            // InternalProblemParser.g:568:6: (lv_shadow_38_0= Shadow )
                            // InternalProblemParser.g:569:7: lv_shadow_38_0= Shadow
                            {
                            lv_shadow_38_0=(Token)match(input,Shadow,FOLLOW_8); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(lv_shadow_38_0, grammarAccess.getAnnotatedStatementAccess().getShadowShadowKeyword_1_4_3_0());
                              						
                            }
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                              							}
                              							setWithLastConsumed(current, "shadow", lv_shadow_38_0 != null, "shadow");
                              						
                            }

                            }


                            }
                            break;

                    }

                    // InternalProblemParser.g:581:5: ( (lv_name_39_0= ruleIdentifier ) )
                    // InternalProblemParser.g:582:6: (lv_name_39_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:582:6: (lv_name_39_0= ruleIdentifier )
                    // InternalProblemParser.g:583:7: lv_name_39_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_4_4_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    lv_name_39_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_39_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_40=(Token)match(input,LeftParenthesis,FOLLOW_22); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_40, grammarAccess.getAnnotatedStatementAccess().getLeftParenthesisKeyword_1_4_5());
                      				
                    }
                    // InternalProblemParser.g:604:5: ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )?
                    int alt17=2;
                    int LA17_0 = input.LA(1);

                    if ( (LA17_0==EOF||(LA17_0>=Concretization && LA17_0<=Aggregator)||(LA17_0>=Container && LA17_0<=Declare)||(LA17_0>=Problem && LA17_0<=Subsets)||LA17_0==Assert||(LA17_0>=Module && LA17_0<=Error)||LA17_0==Multi||(LA17_0>=Atom && LA17_0<=Enum)||(LA17_0>=Pred && LA17_0<=Rule)||LA17_0==ColonColon||LA17_0==As||LA17_0==NumberSign||LA17_0==CommercialAt||LA17_0==RULE_ID||LA17_0==RULE_QUOTED_ID) ) {
                        alt17=1;
                    }
                    switch (alt17) {
                        case 1 :
                            // InternalProblemParser.g:605:6: ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )*
                            {
                            // InternalProblemParser.g:605:6: ( (lv_parameters_41_0= ruleParameter ) )
                            // InternalProblemParser.g:606:7: (lv_parameters_41_0= ruleParameter )
                            {
                            // InternalProblemParser.g:606:7: (lv_parameters_41_0= ruleParameter )
                            // InternalProblemParser.g:607:8: lv_parameters_41_0= ruleParameter
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_4_6_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_parameters_41_0=ruleParameter();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"parameters",
                              									lv_parameters_41_0,
                              									"tools.refinery.language.Problem.Parameter");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:624:6: (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )*
                            loop16:
                            do {
                                int alt16=2;
                                int LA16_0 = input.LA(1);

                                if ( (LA16_0==Comma) ) {
                                    alt16=1;
                                }


                                switch (alt16) {
                            	case 1 :
                            	    // InternalProblemParser.g:625:7: otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) )
                            	    {
                            	    otherlv_42=(Token)match(input,Comma,FOLLOW_24); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_42, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_4_6_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:629:7: ( (lv_parameters_43_0= ruleParameter ) )
                            	    // InternalProblemParser.g:630:8: (lv_parameters_43_0= ruleParameter )
                            	    {
                            	    // InternalProblemParser.g:630:8: (lv_parameters_43_0= ruleParameter )
                            	    // InternalProblemParser.g:631:9: lv_parameters_43_0= ruleParameter
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_4_6_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_parameters_43_0=ruleParameter();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"parameters",
                            	      										lv_parameters_43_0,
                            	      										"tools.refinery.language.Problem.Parameter");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop16;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_44=(Token)match(input,RightParenthesis,FOLLOW_4); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_44, grammarAccess.getAnnotatedStatementAccess().getRightParenthesisKeyword_1_4_7());
                      				
                    }
                    otherlv_45=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_45, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_4_8());
                      				
                    }

                    }


                    }
                    break;
                case 6 :
                    // InternalProblemParser.g:660:4: ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop )
                    {
                    // InternalProblemParser.g:660:4: ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop )
                    // InternalProblemParser.g:661:5: () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop
                    {
                    // InternalProblemParser.g:661:5: ()
                    // InternalProblemParser.g:662:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getPredicateDefinitionAnnotationsAction_1_5_0(),
                      							current);
                      					
                    }

                    }

                    // InternalProblemParser.g:668:5: ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) )
                    int alt19=2;
                    int LA19_0 = input.LA(1);

                    if ( (LA19_0==Error) ) {
                        int LA19_1 = input.LA(2);

                        if ( (LA19_1==Pred) ) {
                            alt19=2;
                        }
                        else if ( ((LA19_1>=Concretization && LA19_1<=Aggregator)||(LA19_1>=Container && LA19_1<=Primitive)||(LA19_1>=Contains && LA19_1<=Opposite)||(LA19_1>=Problem && LA19_1<=Subsets)||LA19_1==Assert||LA19_1==Module||LA19_1==Shadow||LA19_1==Multi||LA19_1==Atom||LA19_1==As||LA19_1==RULE_ID||LA19_1==RULE_QUOTED_ID) ) {
                            alt19=1;
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 19, 1, input);

                            throw nvae;
                        }
                    }
                    else if ( (LA19_0==Shadow||LA19_0==Pred) ) {
                        alt19=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 19, 0, input);

                        throw nvae;
                    }
                    switch (alt19) {
                        case 1 :
                            // InternalProblemParser.g:669:6: ( (lv_kind_47_0= ruleErrorPredicateKind ) )
                            {
                            // InternalProblemParser.g:669:6: ( (lv_kind_47_0= ruleErrorPredicateKind ) )
                            // InternalProblemParser.g:670:7: (lv_kind_47_0= ruleErrorPredicateKind )
                            {
                            // InternalProblemParser.g:670:7: (lv_kind_47_0= ruleErrorPredicateKind )
                            // InternalProblemParser.g:671:8: lv_kind_47_0= ruleErrorPredicateKind
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getKindErrorPredicateKindEnumRuleCall_1_5_1_0_0());
                              							
                            }
                            pushFollow(FOLLOW_8);
                            lv_kind_47_0=ruleErrorPredicateKind();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								set(
                              									current,
                              									"kind",
                              									lv_kind_47_0,
                              									"tools.refinery.language.Problem.ErrorPredicateKind");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }


                            }
                            break;
                        case 2 :
                            // InternalProblemParser.g:689:6: ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred )
                            {
                            // InternalProblemParser.g:689:6: ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred )
                            // InternalProblemParser.g:690:7: ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred
                            {
                            // InternalProblemParser.g:690:7: ( (lv_kind_48_0= rulePredicateKind ) )?
                            int alt18=2;
                            int LA18_0 = input.LA(1);

                            if ( (LA18_0==Shadow||LA18_0==Error) ) {
                                alt18=1;
                            }
                            switch (alt18) {
                                case 1 :
                                    // InternalProblemParser.g:691:8: (lv_kind_48_0= rulePredicateKind )
                                    {
                                    // InternalProblemParser.g:691:8: (lv_kind_48_0= rulePredicateKind )
                                    // InternalProblemParser.g:692:9: lv_kind_48_0= rulePredicateKind
                                    {
                                    if ( state.backtracking==0 ) {

                                      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getKindPredicateKindEnumRuleCall_1_5_1_1_0_0());
                                      								
                                    }
                                    pushFollow(FOLLOW_25);
                                    lv_kind_48_0=rulePredicateKind();

                                    state._fsp--;
                                    if (state.failed) return current;
                                    if ( state.backtracking==0 ) {

                                      									if (current==null) {
                                      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                                      									}
                                      									set(
                                      										current,
                                      										"kind",
                                      										lv_kind_48_0,
                                      										"tools.refinery.language.Problem.PredicateKind");
                                      									afterParserOrEnumRuleCall();
                                      								
                                    }

                                    }


                                    }
                                    break;

                            }

                            otherlv_49=(Token)match(input,Pred,FOLLOW_8); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(otherlv_49, grammarAccess.getAnnotatedStatementAccess().getPredKeyword_1_5_1_1_1());
                              						
                            }

                            }


                            }
                            break;

                    }

                    // InternalProblemParser.g:715:5: ( (lv_name_50_0= ruleIdentifier ) )
                    // InternalProblemParser.g:716:6: (lv_name_50_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:716:6: (lv_name_50_0= ruleIdentifier )
                    // InternalProblemParser.g:717:7: lv_name_50_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_5_2_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    lv_name_50_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_50_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_51=(Token)match(input,LeftParenthesis,FOLLOW_22); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_51, grammarAccess.getAnnotatedStatementAccess().getLeftParenthesisKeyword_1_5_3());
                      				
                    }
                    // InternalProblemParser.g:738:5: ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )?
                    int alt21=2;
                    int LA21_0 = input.LA(1);

                    if ( (LA21_0==EOF||(LA21_0>=Concretization && LA21_0<=Aggregator)||(LA21_0>=Container && LA21_0<=Declare)||(LA21_0>=Problem && LA21_0<=Subsets)||LA21_0==Assert||(LA21_0>=Module && LA21_0<=Error)||LA21_0==Multi||(LA21_0>=Atom && LA21_0<=Enum)||(LA21_0>=Pred && LA21_0<=Rule)||LA21_0==ColonColon||LA21_0==As||LA21_0==NumberSign||LA21_0==CommercialAt||LA21_0==RULE_ID||LA21_0==RULE_QUOTED_ID) ) {
                        alt21=1;
                    }
                    switch (alt21) {
                        case 1 :
                            // InternalProblemParser.g:739:6: ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )*
                            {
                            // InternalProblemParser.g:739:6: ( (lv_parameters_52_0= ruleParameter ) )
                            // InternalProblemParser.g:740:7: (lv_parameters_52_0= ruleParameter )
                            {
                            // InternalProblemParser.g:740:7: (lv_parameters_52_0= ruleParameter )
                            // InternalProblemParser.g:741:8: lv_parameters_52_0= ruleParameter
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_5_4_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_parameters_52_0=ruleParameter();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"parameters",
                              									lv_parameters_52_0,
                              									"tools.refinery.language.Problem.Parameter");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:758:6: (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )*
                            loop20:
                            do {
                                int alt20=2;
                                int LA20_0 = input.LA(1);

                                if ( (LA20_0==Comma) ) {
                                    alt20=1;
                                }


                                switch (alt20) {
                            	case 1 :
                            	    // InternalProblemParser.g:759:7: otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) )
                            	    {
                            	    otherlv_53=(Token)match(input,Comma,FOLLOW_24); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_53, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_5_4_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:763:7: ( (lv_parameters_54_0= ruleParameter ) )
                            	    // InternalProblemParser.g:764:8: (lv_parameters_54_0= ruleParameter )
                            	    {
                            	    // InternalProblemParser.g:764:8: (lv_parameters_54_0= ruleParameter )
                            	    // InternalProblemParser.g:765:9: lv_parameters_54_0= ruleParameter
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_5_4_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_parameters_54_0=ruleParameter();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"parameters",
                            	      										lv_parameters_54_0,
                            	      										"tools.refinery.language.Problem.Parameter");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop20;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_55=(Token)match(input,RightParenthesis,FOLLOW_26); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_55, grammarAccess.getAnnotatedStatementAccess().getRightParenthesisKeyword_1_5_5());
                      				
                    }
                    // InternalProblemParser.g:788:5: (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )?
                    int alt23=2;
                    int LA23_0 = input.LA(1);

                    if ( (LA23_0==Subsets) ) {
                        alt23=1;
                    }
                    switch (alt23) {
                        case 1 :
                            // InternalProblemParser.g:789:6: otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )*
                            {
                            otherlv_56=(Token)match(input,Subsets,FOLLOW_8); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_56, grammarAccess.getAnnotatedStatementAccess().getSubsetsKeyword_1_5_6_0());
                              					
                            }
                            // InternalProblemParser.g:793:6: ( ( ruleQualifiedName ) )
                            // InternalProblemParser.g:794:7: ( ruleQualifiedName )
                            {
                            // InternalProblemParser.g:794:7: ( ruleQualifiedName )
                            // InternalProblemParser.g:795:8: ruleQualifiedName
                            {
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                              								}
                              							
                            }
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getSuperSetsReferenceDeclarationCrossReference_1_5_6_1_0());
                              							
                            }
                            pushFollow(FOLLOW_27);
                            ruleQualifiedName();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:809:6: (otherlv_58= Comma ( ( ruleQualifiedName ) ) )*
                            loop22:
                            do {
                                int alt22=2;
                                int LA22_0 = input.LA(1);

                                if ( (LA22_0==Comma) ) {
                                    alt22=1;
                                }


                                switch (alt22) {
                            	case 1 :
                            	    // InternalProblemParser.g:810:7: otherlv_58= Comma ( ( ruleQualifiedName ) )
                            	    {
                            	    otherlv_58=(Token)match(input,Comma,FOLLOW_8); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_58, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_5_6_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:814:7: ( ( ruleQualifiedName ) )
                            	    // InternalProblemParser.g:815:8: ( ruleQualifiedName )
                            	    {
                            	    // InternalProblemParser.g:815:8: ( ruleQualifiedName )
                            	    // InternalProblemParser.g:816:9: ruleQualifiedName
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      								
                            	    }
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getSuperSetsReferenceDeclarationCrossReference_1_5_6_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_27);
                            	    ruleQualifiedName();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop22;
                                }
                            } while (true);


                            }
                            break;

                    }

                    // InternalProblemParser.g:832:5: (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )?
                    int alt25=2;
                    int LA25_0 = input.LA(1);

                    if ( (LA25_0==LessThanSignHyphenMinusGreaterThanSign) ) {
                        alt25=1;
                    }
                    switch (alt25) {
                        case 1 :
                            // InternalProblemParser.g:833:6: otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )*
                            {
                            otherlv_60=(Token)match(input,LessThanSignHyphenMinusGreaterThanSign,FOLLOW_28); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_60, grammarAccess.getAnnotatedStatementAccess().getLessThanSignHyphenMinusGreaterThanSignKeyword_1_5_7_0());
                              					
                            }
                            // InternalProblemParser.g:837:6: ( (lv_bodies_61_0= ruleConjunction ) )
                            // InternalProblemParser.g:838:7: (lv_bodies_61_0= ruleConjunction )
                            {
                            // InternalProblemParser.g:838:7: (lv_bodies_61_0= ruleConjunction )
                            // InternalProblemParser.g:839:8: lv_bodies_61_0= ruleConjunction
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getBodiesConjunctionParserRuleCall_1_5_7_1_0());
                              							
                            }
                            pushFollow(FOLLOW_29);
                            lv_bodies_61_0=ruleConjunction();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"bodies",
                              									lv_bodies_61_0,
                              									"tools.refinery.language.Problem.Conjunction");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:856:6: (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )*
                            loop24:
                            do {
                                int alt24=2;
                                int LA24_0 = input.LA(1);

                                if ( (LA24_0==Semicolon) ) {
                                    alt24=1;
                                }


                                switch (alt24) {
                            	case 1 :
                            	    // InternalProblemParser.g:857:7: otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) )
                            	    {
                            	    otherlv_62=(Token)match(input,Semicolon,FOLLOW_28); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_62, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_5_7_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:861:7: ( (lv_bodies_63_0= ruleConjunction ) )
                            	    // InternalProblemParser.g:862:8: (lv_bodies_63_0= ruleConjunction )
                            	    {
                            	    // InternalProblemParser.g:862:8: (lv_bodies_63_0= ruleConjunction )
                            	    // InternalProblemParser.g:863:9: lv_bodies_63_0= ruleConjunction
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getBodiesConjunctionParserRuleCall_1_5_7_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_29);
                            	    lv_bodies_63_0=ruleConjunction();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"bodies",
                            	      										lv_bodies_63_0,
                            	      										"tools.refinery.language.Problem.Conjunction");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop24;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_64=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_64, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_5_8());
                      				
                    }

                    }


                    }
                    break;
                case 7 :
                    // InternalProblemParser.g:888:4: ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop )
                    {
                    // InternalProblemParser.g:888:4: ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop )
                    // InternalProblemParser.g:889:5: () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop
                    {
                    // InternalProblemParser.g:889:5: ()
                    // InternalProblemParser.g:890:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getFunctionDefinitionAnnotationsAction_1_6_0(),
                      							current);
                      					
                    }

                    }

                    // InternalProblemParser.g:896:5: ( (lv_shadow_66_0= Shadow ) )?
                    int alt26=2;
                    alt26 = dfa26.predict(input);
                    switch (alt26) {
                        case 1 :
                            // InternalProblemParser.g:897:6: (lv_shadow_66_0= Shadow )
                            {
                            // InternalProblemParser.g:897:6: (lv_shadow_66_0= Shadow )
                            // InternalProblemParser.g:898:7: lv_shadow_66_0= Shadow
                            {
                            lv_shadow_66_0=(Token)match(input,Shadow,FOLLOW_8); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							newLeafNode(lv_shadow_66_0, grammarAccess.getAnnotatedStatementAccess().getShadowShadowKeyword_1_6_1_0());
                              						
                            }
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                              							}
                              							setWithLastConsumed(current, "shadow", lv_shadow_66_0 != null, "shadow");
                              						
                            }

                            }


                            }
                            break;

                    }

                    // InternalProblemParser.g:910:5: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:911:6: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:911:6: ( ruleQualifiedName )
                    // InternalProblemParser.g:912:7: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElement(grammarAccess.getAnnotatedStatementRule());
                      							}
                      						
                    }
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getFunctionTypeRelationCrossReference_1_6_2_0());
                      						
                    }
                    pushFollow(FOLLOW_8);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:926:5: ( (lv_name_68_0= ruleIdentifier ) )
                    // InternalProblemParser.g:927:6: (lv_name_68_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:927:6: (lv_name_68_0= ruleIdentifier )
                    // InternalProblemParser.g:928:7: lv_name_68_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_6_3_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    lv_name_68_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_68_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_69=(Token)match(input,LeftParenthesis,FOLLOW_22); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_69, grammarAccess.getAnnotatedStatementAccess().getLeftParenthesisKeyword_1_6_4());
                      				
                    }
                    // InternalProblemParser.g:949:5: ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )?
                    int alt28=2;
                    int LA28_0 = input.LA(1);

                    if ( (LA28_0==EOF||(LA28_0>=Concretization && LA28_0<=Aggregator)||(LA28_0>=Container && LA28_0<=Declare)||(LA28_0>=Problem && LA28_0<=Subsets)||LA28_0==Assert||(LA28_0>=Module && LA28_0<=Error)||LA28_0==Multi||(LA28_0>=Atom && LA28_0<=Enum)||(LA28_0>=Pred && LA28_0<=Rule)||LA28_0==ColonColon||LA28_0==As||LA28_0==NumberSign||LA28_0==CommercialAt||LA28_0==RULE_ID||LA28_0==RULE_QUOTED_ID) ) {
                        alt28=1;
                    }
                    switch (alt28) {
                        case 1 :
                            // InternalProblemParser.g:950:6: ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )*
                            {
                            // InternalProblemParser.g:950:6: ( (lv_parameters_70_0= ruleParameter ) )
                            // InternalProblemParser.g:951:7: (lv_parameters_70_0= ruleParameter )
                            {
                            // InternalProblemParser.g:951:7: (lv_parameters_70_0= ruleParameter )
                            // InternalProblemParser.g:952:8: lv_parameters_70_0= ruleParameter
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_6_5_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_parameters_70_0=ruleParameter();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"parameters",
                              									lv_parameters_70_0,
                              									"tools.refinery.language.Problem.Parameter");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:969:6: (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )*
                            loop27:
                            do {
                                int alt27=2;
                                int LA27_0 = input.LA(1);

                                if ( (LA27_0==Comma) ) {
                                    alt27=1;
                                }


                                switch (alt27) {
                            	case 1 :
                            	    // InternalProblemParser.g:970:7: otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) )
                            	    {
                            	    otherlv_71=(Token)match(input,Comma,FOLLOW_24); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_71, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_6_5_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:974:7: ( (lv_parameters_72_0= ruleParameter ) )
                            	    // InternalProblemParser.g:975:8: (lv_parameters_72_0= ruleParameter )
                            	    {
                            	    // InternalProblemParser.g:975:8: (lv_parameters_72_0= ruleParameter )
                            	    // InternalProblemParser.g:976:9: lv_parameters_72_0= ruleParameter
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_6_5_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_parameters_72_0=ruleParameter();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"parameters",
                            	      										lv_parameters_72_0,
                            	      										"tools.refinery.language.Problem.Parameter");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop27;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_73=(Token)match(input,RightParenthesis,FOLLOW_30); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_73, grammarAccess.getAnnotatedStatementAccess().getRightParenthesisKeyword_1_6_6());
                      				
                    }
                    // InternalProblemParser.g:999:5: (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )?
                    int alt30=2;
                    int LA30_0 = input.LA(1);

                    if ( (LA30_0==EqualsSign) ) {
                        alt30=1;
                    }
                    switch (alt30) {
                        case 1 :
                            // InternalProblemParser.g:1000:6: otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )*
                            {
                            otherlv_74=(Token)match(input,EqualsSign,FOLLOW_28); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_74, grammarAccess.getAnnotatedStatementAccess().getEqualsSignKeyword_1_6_7_0());
                              					
                            }
                            // InternalProblemParser.g:1004:6: ( (lv_cases_75_0= ruleCase ) )
                            // InternalProblemParser.g:1005:7: (lv_cases_75_0= ruleCase )
                            {
                            // InternalProblemParser.g:1005:7: (lv_cases_75_0= ruleCase )
                            // InternalProblemParser.g:1006:8: lv_cases_75_0= ruleCase
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getCasesCaseParserRuleCall_1_6_7_1_0());
                              							
                            }
                            pushFollow(FOLLOW_29);
                            lv_cases_75_0=ruleCase();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"cases",
                              									lv_cases_75_0,
                              									"tools.refinery.language.Problem.Case");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:1023:6: (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )*
                            loop29:
                            do {
                                int alt29=2;
                                int LA29_0 = input.LA(1);

                                if ( (LA29_0==Semicolon) ) {
                                    alt29=1;
                                }


                                switch (alt29) {
                            	case 1 :
                            	    // InternalProblemParser.g:1024:7: otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) )
                            	    {
                            	    otherlv_76=(Token)match(input,Semicolon,FOLLOW_28); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_76, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_6_7_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:1028:7: ( (lv_cases_77_0= ruleCase ) )
                            	    // InternalProblemParser.g:1029:8: (lv_cases_77_0= ruleCase )
                            	    {
                            	    // InternalProblemParser.g:1029:8: (lv_cases_77_0= ruleCase )
                            	    // InternalProblemParser.g:1030:9: lv_cases_77_0= ruleCase
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getCasesCaseParserRuleCall_1_6_7_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_29);
                            	    lv_cases_77_0=ruleCase();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"cases",
                            	      										lv_cases_77_0,
                            	      										"tools.refinery.language.Problem.Case");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop29;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_78=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_78, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_6_8());
                      				
                    }

                    }


                    }
                    break;
                case 8 :
                    // InternalProblemParser.g:1055:4: ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop )
                    {
                    // InternalProblemParser.g:1055:4: ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop )
                    // InternalProblemParser.g:1056:5: () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop
                    {
                    // InternalProblemParser.g:1056:5: ()
                    // InternalProblemParser.g:1057:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getRuleDefinitionAnnotationsAction_1_7_0(),
                      							current);
                      					
                    }

                    }

                    // InternalProblemParser.g:1063:5: ( (lv_kind_80_0= ruleRuleKind ) )?
                    int alt31=2;
                    int LA31_0 = input.LA(1);

                    if ( ((LA31_0>=Concretization && LA31_0<=Propagation)||LA31_0==Decision) ) {
                        alt31=1;
                    }
                    switch (alt31) {
                        case 1 :
                            // InternalProblemParser.g:1064:6: (lv_kind_80_0= ruleRuleKind )
                            {
                            // InternalProblemParser.g:1064:6: (lv_kind_80_0= ruleRuleKind )
                            // InternalProblemParser.g:1065:7: lv_kind_80_0= ruleRuleKind
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getKindRuleKindEnumRuleCall_1_7_1_0());
                              						
                            }
                            pushFollow(FOLLOW_31);
                            lv_kind_80_0=ruleRuleKind();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              							}
                              							set(
                              								current,
                              								"kind",
                              								lv_kind_80_0,
                              								"tools.refinery.language.Problem.RuleKind");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }
                            break;

                    }

                    otherlv_81=(Token)match(input,Rule,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_81, grammarAccess.getAnnotatedStatementAccess().getRuleKeyword_1_7_2());
                      				
                    }
                    // InternalProblemParser.g:1086:5: ( (lv_name_82_0= ruleIdentifier ) )
                    // InternalProblemParser.g:1087:6: (lv_name_82_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:1087:6: (lv_name_82_0= ruleIdentifier )
                    // InternalProblemParser.g:1088:7: lv_name_82_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_7_3_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    lv_name_82_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_82_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_83=(Token)match(input,LeftParenthesis,FOLLOW_22); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_83, grammarAccess.getAnnotatedStatementAccess().getLeftParenthesisKeyword_1_7_4());
                      				
                    }
                    // InternalProblemParser.g:1109:5: ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )?
                    int alt33=2;
                    int LA33_0 = input.LA(1);

                    if ( (LA33_0==EOF||(LA33_0>=Concretization && LA33_0<=Aggregator)||(LA33_0>=Container && LA33_0<=Declare)||(LA33_0>=Problem && LA33_0<=Subsets)||LA33_0==Assert||(LA33_0>=Module && LA33_0<=Error)||LA33_0==Multi||(LA33_0>=Atom && LA33_0<=Enum)||(LA33_0>=Pred && LA33_0<=Rule)||LA33_0==ColonColon||LA33_0==As||LA33_0==NumberSign||LA33_0==CommercialAt||LA33_0==RULE_ID||LA33_0==RULE_QUOTED_ID) ) {
                        alt33=1;
                    }
                    switch (alt33) {
                        case 1 :
                            // InternalProblemParser.g:1110:6: ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )*
                            {
                            // InternalProblemParser.g:1110:6: ( (lv_parameters_84_0= ruleParameter ) )
                            // InternalProblemParser.g:1111:7: (lv_parameters_84_0= ruleParameter )
                            {
                            // InternalProblemParser.g:1111:7: (lv_parameters_84_0= ruleParameter )
                            // InternalProblemParser.g:1112:8: lv_parameters_84_0= ruleParameter
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_7_5_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_parameters_84_0=ruleParameter();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"parameters",
                              									lv_parameters_84_0,
                              									"tools.refinery.language.Problem.Parameter");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:1129:6: (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )*
                            loop32:
                            do {
                                int alt32=2;
                                int LA32_0 = input.LA(1);

                                if ( (LA32_0==Comma) ) {
                                    alt32=1;
                                }


                                switch (alt32) {
                            	case 1 :
                            	    // InternalProblemParser.g:1130:7: otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) )
                            	    {
                            	    otherlv_85=(Token)match(input,Comma,FOLLOW_24); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_85, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_7_5_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:1134:7: ( (lv_parameters_86_0= ruleParameter ) )
                            	    // InternalProblemParser.g:1135:8: (lv_parameters_86_0= ruleParameter )
                            	    {
                            	    // InternalProblemParser.g:1135:8: (lv_parameters_86_0= ruleParameter )
                            	    // InternalProblemParser.g:1136:9: lv_parameters_86_0= ruleParameter
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_7_5_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_parameters_86_0=ruleParameter();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"parameters",
                            	      										lv_parameters_86_0,
                            	      										"tools.refinery.language.Problem.Parameter");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop32;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_87=(Token)match(input,RightParenthesis,FOLLOW_32); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_87, grammarAccess.getAnnotatedStatementAccess().getRightParenthesisKeyword_1_7_6());
                      				
                    }
                    // InternalProblemParser.g:1159:5: (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )?
                    int alt35=2;
                    int LA35_0 = input.LA(1);

                    if ( (LA35_0==LessThanSignHyphenMinusGreaterThanSign) ) {
                        alt35=1;
                    }
                    switch (alt35) {
                        case 1 :
                            // InternalProblemParser.g:1160:6: otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )*
                            {
                            otherlv_88=(Token)match(input,LessThanSignHyphenMinusGreaterThanSign,FOLLOW_28); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_88, grammarAccess.getAnnotatedStatementAccess().getLessThanSignHyphenMinusGreaterThanSignKeyword_1_7_7_0());
                              					
                            }
                            // InternalProblemParser.g:1164:6: ( (lv_preconditions_89_0= ruleConjunction ) )
                            // InternalProblemParser.g:1165:7: (lv_preconditions_89_0= ruleConjunction )
                            {
                            // InternalProblemParser.g:1165:7: (lv_preconditions_89_0= ruleConjunction )
                            // InternalProblemParser.g:1166:8: lv_preconditions_89_0= ruleConjunction
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getPreconditionsConjunctionParserRuleCall_1_7_7_1_0());
                              							
                            }
                            pushFollow(FOLLOW_33);
                            lv_preconditions_89_0=ruleConjunction();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"preconditions",
                              									lv_preconditions_89_0,
                              									"tools.refinery.language.Problem.Conjunction");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:1183:6: (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )*
                            loop34:
                            do {
                                int alt34=2;
                                int LA34_0 = input.LA(1);

                                if ( (LA34_0==Semicolon) ) {
                                    alt34=1;
                                }


                                switch (alt34) {
                            	case 1 :
                            	    // InternalProblemParser.g:1184:7: otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) )
                            	    {
                            	    otherlv_90=(Token)match(input,Semicolon,FOLLOW_28); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_90, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_7_7_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:1188:7: ( (lv_preconditions_91_0= ruleConjunction ) )
                            	    // InternalProblemParser.g:1189:8: (lv_preconditions_91_0= ruleConjunction )
                            	    {
                            	    // InternalProblemParser.g:1189:8: (lv_preconditions_91_0= ruleConjunction )
                            	    // InternalProblemParser.g:1190:9: lv_preconditions_91_0= ruleConjunction
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getPreconditionsConjunctionParserRuleCall_1_7_7_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_33);
                            	    lv_preconditions_91_0=ruleConjunction();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"preconditions",
                            	      										lv_preconditions_91_0,
                            	      										"tools.refinery.language.Problem.Conjunction");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop34;
                                }
                            } while (true);


                            }
                            break;

                    }

                    // InternalProblemParser.g:1209:5: (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )?
                    int alt37=2;
                    int LA37_0 = input.LA(1);

                    if ( (LA37_0==EqualsSignEqualsSignGreaterThanSign) ) {
                        alt37=1;
                    }
                    switch (alt37) {
                        case 1 :
                            // InternalProblemParser.g:1210:6: otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )*
                            {
                            otherlv_92=(Token)match(input,EqualsSignEqualsSignGreaterThanSign,FOLLOW_34); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_92, grammarAccess.getAnnotatedStatementAccess().getEqualsSignEqualsSignGreaterThanSignKeyword_1_7_8_0());
                              					
                            }
                            // InternalProblemParser.g:1214:6: ( (lv_consequents_93_0= ruleConsequent ) )
                            // InternalProblemParser.g:1215:7: (lv_consequents_93_0= ruleConsequent )
                            {
                            // InternalProblemParser.g:1215:7: (lv_consequents_93_0= ruleConsequent )
                            // InternalProblemParser.g:1216:8: lv_consequents_93_0= ruleConsequent
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getConsequentsConsequentParserRuleCall_1_7_8_1_0());
                              							
                            }
                            pushFollow(FOLLOW_29);
                            lv_consequents_93_0=ruleConsequent();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"consequents",
                              									lv_consequents_93_0,
                              									"tools.refinery.language.Problem.Consequent");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:1233:6: (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )*
                            loop36:
                            do {
                                int alt36=2;
                                int LA36_0 = input.LA(1);

                                if ( (LA36_0==Semicolon) ) {
                                    alt36=1;
                                }


                                switch (alt36) {
                            	case 1 :
                            	    // InternalProblemParser.g:1234:7: otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) )
                            	    {
                            	    otherlv_94=(Token)match(input,Semicolon,FOLLOW_34); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_94, grammarAccess.getAnnotatedStatementAccess().getSemicolonKeyword_1_7_8_2_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:1238:7: ( (lv_consequents_95_0= ruleConsequent ) )
                            	    // InternalProblemParser.g:1239:8: (lv_consequents_95_0= ruleConsequent )
                            	    {
                            	    // InternalProblemParser.g:1239:8: (lv_consequents_95_0= ruleConsequent )
                            	    // InternalProblemParser.g:1240:9: lv_consequents_95_0= ruleConsequent
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getConsequentsConsequentParserRuleCall_1_7_8_2_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_29);
                            	    lv_consequents_95_0=ruleConsequent();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"consequents",
                            	      										lv_consequents_95_0,
                            	      										"tools.refinery.language.Problem.Consequent");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop36;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_96=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_96, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_7_9());
                      				
                    }

                    }


                    }
                    break;
                case 9 :
                    // InternalProblemParser.g:1265:4: ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop )
                    {
                    // InternalProblemParser.g:1265:4: ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop )
                    // InternalProblemParser.g:1266:5: () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop
                    {
                    // InternalProblemParser.g:1266:5: ()
                    // InternalProblemParser.g:1267:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getAnnotationDeclarationAnnotationsAction_1_8_0(),
                      							current);
                      					
                    }

                    }

                    otherlv_98=(Token)match(input,NumberSign,FOLLOW_25); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_98, grammarAccess.getAnnotatedStatementAccess().getNumberSignKeyword_1_8_1());
                      				
                    }
                    otherlv_99=(Token)match(input,Pred,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_99, grammarAccess.getAnnotatedStatementAccess().getPredKeyword_1_8_2());
                      				
                    }
                    // InternalProblemParser.g:1281:5: ( (lv_name_100_0= ruleIdentifier ) )
                    // InternalProblemParser.g:1282:6: (lv_name_100_0= ruleIdentifier )
                    {
                    // InternalProblemParser.g:1282:6: (lv_name_100_0= ruleIdentifier )
                    // InternalProblemParser.g:1283:7: lv_name_100_0= ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNameIdentifierParserRuleCall_1_8_3_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    lv_name_100_0=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							set(
                      								current,
                      								"name",
                      								lv_name_100_0,
                      								"tools.refinery.language.Problem.Identifier");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_101=(Token)match(input,LeftParenthesis,FOLLOW_22); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_101, grammarAccess.getAnnotatedStatementAccess().getLeftParenthesisKeyword_1_8_4());
                      				
                    }
                    // InternalProblemParser.g:1304:5: ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )?
                    int alt39=2;
                    int LA39_0 = input.LA(1);

                    if ( (LA39_0==EOF||(LA39_0>=Concretization && LA39_0<=Aggregator)||(LA39_0>=Container && LA39_0<=Declare)||(LA39_0>=Problem && LA39_0<=Subsets)||LA39_0==Assert||(LA39_0>=Module && LA39_0<=Error)||LA39_0==Multi||(LA39_0>=Atom && LA39_0<=Enum)||(LA39_0>=Pred && LA39_0<=Rule)||LA39_0==ColonColon||LA39_0==As||LA39_0==NumberSign||LA39_0==CommercialAt||LA39_0==RULE_ID||LA39_0==RULE_QUOTED_ID) ) {
                        alt39=1;
                    }
                    switch (alt39) {
                        case 1 :
                            // InternalProblemParser.g:1305:6: ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )*
                            {
                            // InternalProblemParser.g:1305:6: ( (lv_parameters_102_0= ruleParameter ) )
                            // InternalProblemParser.g:1306:7: (lv_parameters_102_0= ruleParameter )
                            {
                            // InternalProblemParser.g:1306:7: (lv_parameters_102_0= ruleParameter )
                            // InternalProblemParser.g:1307:8: lv_parameters_102_0= ruleParameter
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_8_5_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_parameters_102_0=ruleParameter();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              								}
                              								add(
                              									current,
                              									"parameters",
                              									lv_parameters_102_0,
                              									"tools.refinery.language.Problem.Parameter");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:1324:6: (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )*
                            loop38:
                            do {
                                int alt38=2;
                                int LA38_0 = input.LA(1);

                                if ( (LA38_0==Comma) ) {
                                    alt38=1;
                                }


                                switch (alt38) {
                            	case 1 :
                            	    // InternalProblemParser.g:1325:7: otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) )
                            	    {
                            	    otherlv_103=(Token)match(input,Comma,FOLLOW_24); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_103, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_8_5_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:1329:7: ( (lv_parameters_104_0= ruleParameter ) )
                            	    // InternalProblemParser.g:1330:8: (lv_parameters_104_0= ruleParameter )
                            	    {
                            	    // InternalProblemParser.g:1330:8: (lv_parameters_104_0= ruleParameter )
                            	    // InternalProblemParser.g:1331:9: lv_parameters_104_0= ruleParameter
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getParametersParameterParserRuleCall_1_8_5_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_parameters_104_0=ruleParameter();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"parameters",
                            	      										lv_parameters_104_0,
                            	      										"tools.refinery.language.Problem.Parameter");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop38;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_105=(Token)match(input,RightParenthesis,FOLLOW_4); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_105, grammarAccess.getAnnotatedStatementAccess().getRightParenthesisKeyword_1_8_6());
                      				
                    }
                    otherlv_106=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_106, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_8_7());
                      				
                    }

                    }


                    }
                    break;
                case 10 :
                    // InternalProblemParser.g:1360:4: ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop )
                    {
                    // InternalProblemParser.g:1360:4: ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop )
                    // InternalProblemParser.g:1361:5: () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop
                    {
                    // InternalProblemParser.g:1361:5: ()
                    // InternalProblemParser.g:1362:6: 
                    {
                    if ( state.backtracking==0 ) {

                      						current = forceCreateModelElementAndSet(
                      							grammarAccess.getAnnotatedStatementAccess().getNodeDeclarationAnnotationsAction_1_9_0(),
                      							current);
                      					
                    }

                    }

                    // InternalProblemParser.g:1368:5: (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) )
                    int alt41=2;
                    int LA41_0 = input.LA(1);

                    if ( (LA41_0==Declare) ) {
                        switch ( input.LA(2) ) {
                        case Concretization:
                        case Propagation:
                        case Aggregator:
                        case Container:
                        case Primitive:
                        case Contains:
                        case Datatype:
                        case Decision:
                        case Opposite:
                        case Problem:
                        case Subsets:
                        case Assert:
                        case Module:
                        case Shadow:
                        case As:
                        case CommercialAt:
                        case RULE_ID:
                        case RULE_QUOTED_ID:
                            {
                            alt41=1;
                            }
                            break;
                        case Atom:
                            {
                            int LA41_4 = input.LA(3);

                            if ( (LA41_4==Comma||LA41_4==FullStop) ) {
                                alt41=1;
                            }
                            else if ( ((LA41_4>=Concretization && LA41_4<=Aggregator)||(LA41_4>=Container && LA41_4<=Primitive)||(LA41_4>=Contains && LA41_4<=Opposite)||(LA41_4>=Problem && LA41_4<=Subsets)||LA41_4==Assert||LA41_4==Module||LA41_4==Shadow||LA41_4==Multi||LA41_4==Atom||LA41_4==As||LA41_4==CommercialAt||LA41_4==RULE_ID||LA41_4==RULE_QUOTED_ID) ) {
                                alt41=2;
                            }
                            else {
                                if (state.backtracking>0) {state.failed=true; return current;}
                                NoViableAltException nvae =
                                    new NoViableAltException("", 41, 4, input);

                                throw nvae;
                            }
                            }
                            break;
                        case Multi:
                            {
                            int LA41_5 = input.LA(3);

                            if ( ((LA41_5>=Concretization && LA41_5<=Aggregator)||(LA41_5>=Container && LA41_5<=Primitive)||(LA41_5>=Contains && LA41_5<=Opposite)||(LA41_5>=Problem && LA41_5<=Subsets)||LA41_5==Assert||LA41_5==Module||LA41_5==Shadow||LA41_5==Multi||LA41_5==Atom||LA41_5==As||LA41_5==CommercialAt||LA41_5==RULE_ID||LA41_5==RULE_QUOTED_ID) ) {
                                alt41=2;
                            }
                            else if ( (LA41_5==Comma||LA41_5==FullStop) ) {
                                alt41=1;
                            }
                            else {
                                if (state.backtracking>0) {state.failed=true; return current;}
                                NoViableAltException nvae =
                                    new NoViableAltException("", 41, 5, input);

                                throw nvae;
                            }
                            }
                            break;
                        default:
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 41, 1, input);

                            throw nvae;
                        }

                    }
                    else if ( (LA41_0==Multi||LA41_0==Atom) ) {
                        alt41=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 41, 0, input);

                        throw nvae;
                    }
                    switch (alt41) {
                        case 1 :
                            // InternalProblemParser.g:1369:6: otherlv_108= Declare
                            {
                            otherlv_108=(Token)match(input,Declare,FOLLOW_16); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              						newLeafNode(otherlv_108, grammarAccess.getAnnotatedStatementAccess().getDeclareKeyword_1_9_1_0());
                              					
                            }

                            }
                            break;
                        case 2 :
                            // InternalProblemParser.g:1374:6: ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) )
                            {
                            // InternalProblemParser.g:1374:6: ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) )
                            // InternalProblemParser.g:1375:7: (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) )
                            {
                            // InternalProblemParser.g:1375:7: (otherlv_109= Declare )?
                            int alt40=2;
                            int LA40_0 = input.LA(1);

                            if ( (LA40_0==Declare) ) {
                                alt40=1;
                            }
                            switch (alt40) {
                                case 1 :
                                    // InternalProblemParser.g:1376:8: otherlv_109= Declare
                                    {
                                    otherlv_109=(Token)match(input,Declare,FOLLOW_6); if (state.failed) return current;
                                    if ( state.backtracking==0 ) {

                                      								newLeafNode(otherlv_109, grammarAccess.getAnnotatedStatementAccess().getDeclareKeyword_1_9_1_1_0());
                                      							
                                    }

                                    }
                                    break;

                            }

                            // InternalProblemParser.g:1381:7: ( (lv_kind_110_0= ruleNodeKind ) )
                            // InternalProblemParser.g:1382:8: (lv_kind_110_0= ruleNodeKind )
                            {
                            // InternalProblemParser.g:1382:8: (lv_kind_110_0= ruleNodeKind )
                            // InternalProblemParser.g:1383:9: lv_kind_110_0= ruleNodeKind
                            {
                            if ( state.backtracking==0 ) {

                              									newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getKindNodeKindEnumRuleCall_1_9_1_1_1_0());
                              								
                            }
                            pushFollow(FOLLOW_16);
                            lv_kind_110_0=ruleNodeKind();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              									if (current==null) {
                              										current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                              									}
                              									set(
                              										current,
                              										"kind",
                              										lv_kind_110_0,
                              										"tools.refinery.language.Problem.NodeKind");
                              									afterParserOrEnumRuleCall();
                              								
                            }

                            }


                            }


                            }


                            }
                            break;

                    }

                    // InternalProblemParser.g:1402:5: ( (lv_nodes_111_0= ruleEnumLiteral ) )
                    // InternalProblemParser.g:1403:6: (lv_nodes_111_0= ruleEnumLiteral )
                    {
                    // InternalProblemParser.g:1403:6: (lv_nodes_111_0= ruleEnumLiteral )
                    // InternalProblemParser.g:1404:7: lv_nodes_111_0= ruleEnumLiteral
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNodesEnumLiteralParserRuleCall_1_9_2_0());
                      						
                    }
                    pushFollow(FOLLOW_35);
                    lv_nodes_111_0=ruleEnumLiteral();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                      							}
                      							add(
                      								current,
                      								"nodes",
                      								lv_nodes_111_0,
                      								"tools.refinery.language.Problem.EnumLiteral");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:1421:5: (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )*
                    loop42:
                    do {
                        int alt42=2;
                        int LA42_0 = input.LA(1);

                        if ( (LA42_0==Comma) ) {
                            alt42=1;
                        }


                        switch (alt42) {
                    	case 1 :
                    	    // InternalProblemParser.g:1422:6: otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) )
                    	    {
                    	    otherlv_112=(Token)match(input,Comma,FOLLOW_16); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      						newLeafNode(otherlv_112, grammarAccess.getAnnotatedStatementAccess().getCommaKeyword_1_9_3_0());
                    	      					
                    	    }
                    	    // InternalProblemParser.g:1426:6: ( (lv_nodes_113_0= ruleEnumLiteral ) )
                    	    // InternalProblemParser.g:1427:7: (lv_nodes_113_0= ruleEnumLiteral )
                    	    {
                    	    // InternalProblemParser.g:1427:7: (lv_nodes_113_0= ruleEnumLiteral )
                    	    // InternalProblemParser.g:1428:8: lv_nodes_113_0= ruleEnumLiteral
                    	    {
                    	    if ( state.backtracking==0 ) {

                    	      								newCompositeNode(grammarAccess.getAnnotatedStatementAccess().getNodesEnumLiteralParserRuleCall_1_9_3_1_0());
                    	      							
                    	    }
                    	    pushFollow(FOLLOW_35);
                    	    lv_nodes_113_0=ruleEnumLiteral();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      								if (current==null) {
                    	      									current = createModelElementForParent(grammarAccess.getAnnotatedStatementRule());
                    	      								}
                    	      								add(
                    	      									current,
                    	      									"nodes",
                    	      									lv_nodes_113_0,
                    	      									"tools.refinery.language.Problem.EnumLiteral");
                    	      								afterParserOrEnumRuleCall();
                    	      							
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop42;
                        }
                    } while (true);

                    otherlv_114=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_114, grammarAccess.getAnnotatedStatementAccess().getFullStopKeyword_1_9_4());
                      				
                    }

                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAnnotatedStatement"


    // $ANTLR start "entryRuleAnnotationContainer"
    // InternalProblemParser.g:1456:1: entryRuleAnnotationContainer returns [EObject current=null] : iv_ruleAnnotationContainer= ruleAnnotationContainer EOF ;
    public final EObject entryRuleAnnotationContainer() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAnnotationContainer = null;


        try {
            // InternalProblemParser.g:1456:60: (iv_ruleAnnotationContainer= ruleAnnotationContainer EOF )
            // InternalProblemParser.g:1457:2: iv_ruleAnnotationContainer= ruleAnnotationContainer EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAnnotationContainerRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAnnotationContainer=ruleAnnotationContainer();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAnnotationContainer; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAnnotationContainer"


    // $ANTLR start "ruleAnnotationContainer"
    // InternalProblemParser.g:1463:1: ruleAnnotationContainer returns [EObject current=null] : ( () (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )* ) ;
    public final EObject ruleAnnotationContainer() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        EObject lv_annotations_2_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1469:2: ( ( () (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )* ) )
            // InternalProblemParser.g:1470:2: ( () (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )* )
            {
            // InternalProblemParser.g:1470:2: ( () (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )* )
            // InternalProblemParser.g:1471:3: () (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )*
            {
            // InternalProblemParser.g:1471:3: ()
            // InternalProblemParser.g:1472:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getAnnotationContainerAccess().getAnnotationContainerAction_0(),
              					current);
              			
            }

            }

            // InternalProblemParser.g:1478:3: (otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) ) )*
            loop44:
            do {
                int alt44=2;
                int LA44_0 = input.LA(1);

                if ( (LA44_0==CommercialAt) ) {
                    alt44=1;
                }


                switch (alt44) {
            	case 1 :
            	    // InternalProblemParser.g:1479:4: otherlv_1= CommercialAt ( (lv_annotations_2_0= ruleAnnotation ) )
            	    {
            	    otherlv_1=(Token)match(input,CommercialAt,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_1, grammarAccess.getAnnotationContainerAccess().getCommercialAtKeyword_1_0());
            	      			
            	    }
            	    // InternalProblemParser.g:1483:4: ( (lv_annotations_2_0= ruleAnnotation ) )
            	    // InternalProblemParser.g:1484:5: (lv_annotations_2_0= ruleAnnotation )
            	    {
            	    // InternalProblemParser.g:1484:5: (lv_annotations_2_0= ruleAnnotation )
            	    // InternalProblemParser.g:1485:6: lv_annotations_2_0= ruleAnnotation
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getAnnotationContainerAccess().getAnnotationsAnnotationParserRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_36);
            	    lv_annotations_2_0=ruleAnnotation();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getAnnotationContainerRule());
            	      						}
            	      						add(
            	      							current,
            	      							"annotations",
            	      							lv_annotations_2_0,
            	      							"tools.refinery.language.Problem.Annotation");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop44;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAnnotationContainer"


    // $ANTLR start "entryRuleTopLevelAnnotation"
    // InternalProblemParser.g:1507:1: entryRuleTopLevelAnnotation returns [EObject current=null] : iv_ruleTopLevelAnnotation= ruleTopLevelAnnotation EOF ;
    public final EObject entryRuleTopLevelAnnotation() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTopLevelAnnotation = null;


        try {
            // InternalProblemParser.g:1507:59: (iv_ruleTopLevelAnnotation= ruleTopLevelAnnotation EOF )
            // InternalProblemParser.g:1508:2: iv_ruleTopLevelAnnotation= ruleTopLevelAnnotation EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTopLevelAnnotationRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleTopLevelAnnotation=ruleTopLevelAnnotation();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTopLevelAnnotation; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleTopLevelAnnotation"


    // $ANTLR start "ruleTopLevelAnnotation"
    // InternalProblemParser.g:1514:1: ruleTopLevelAnnotation returns [EObject current=null] : (otherlv_0= NumberSign ( (lv_annotation_1_0= ruleAnnotation ) ) otherlv_2= FullStop ) ;
    public final EObject ruleTopLevelAnnotation() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        EObject lv_annotation_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1520:2: ( (otherlv_0= NumberSign ( (lv_annotation_1_0= ruleAnnotation ) ) otherlv_2= FullStop ) )
            // InternalProblemParser.g:1521:2: (otherlv_0= NumberSign ( (lv_annotation_1_0= ruleAnnotation ) ) otherlv_2= FullStop )
            {
            // InternalProblemParser.g:1521:2: (otherlv_0= NumberSign ( (lv_annotation_1_0= ruleAnnotation ) ) otherlv_2= FullStop )
            // InternalProblemParser.g:1522:3: otherlv_0= NumberSign ( (lv_annotation_1_0= ruleAnnotation ) ) otherlv_2= FullStop
            {
            otherlv_0=(Token)match(input,NumberSign,FOLLOW_8); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getTopLevelAnnotationAccess().getNumberSignKeyword_0());
              		
            }
            // InternalProblemParser.g:1526:3: ( (lv_annotation_1_0= ruleAnnotation ) )
            // InternalProblemParser.g:1527:4: (lv_annotation_1_0= ruleAnnotation )
            {
            // InternalProblemParser.g:1527:4: (lv_annotation_1_0= ruleAnnotation )
            // InternalProblemParser.g:1528:5: lv_annotation_1_0= ruleAnnotation
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getTopLevelAnnotationAccess().getAnnotationAnnotationParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_4);
            lv_annotation_1_0=ruleAnnotation();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getTopLevelAnnotationRule());
              					}
              					set(
              						current,
              						"annotation",
              						lv_annotation_1_0,
              						"tools.refinery.language.Problem.Annotation");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            otherlv_2=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_2, grammarAccess.getTopLevelAnnotationAccess().getFullStopKeyword_2());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleTopLevelAnnotation"


    // $ANTLR start "entryRuleAnnotation"
    // InternalProblemParser.g:1553:1: entryRuleAnnotation returns [EObject current=null] : iv_ruleAnnotation= ruleAnnotation EOF ;
    public final EObject entryRuleAnnotation() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAnnotation = null;


        try {
            // InternalProblemParser.g:1553:51: (iv_ruleAnnotation= ruleAnnotation EOF )
            // InternalProblemParser.g:1554:2: iv_ruleAnnotation= ruleAnnotation EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAnnotationRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAnnotation=ruleAnnotation();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAnnotation; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAnnotation"


    // $ANTLR start "ruleAnnotation"
    // InternalProblemParser.g:1560:1: ruleAnnotation returns [EObject current=null] : ( () ( ( ruleQualifiedName ) ) (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )? ) ;
    public final EObject ruleAnnotation() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        EObject lv_arguments_3_0 = null;

        EObject lv_arguments_5_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1566:2: ( ( () ( ( ruleQualifiedName ) ) (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )? ) )
            // InternalProblemParser.g:1567:2: ( () ( ( ruleQualifiedName ) ) (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )? )
            {
            // InternalProblemParser.g:1567:2: ( () ( ( ruleQualifiedName ) ) (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )? )
            // InternalProblemParser.g:1568:3: () ( ( ruleQualifiedName ) ) (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )?
            {
            // InternalProblemParser.g:1568:3: ()
            // InternalProblemParser.g:1569:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getAnnotationAccess().getAnnotationAction_0(),
              					current);
              			
            }

            }

            // InternalProblemParser.g:1575:3: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:1576:4: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:1576:4: ( ruleQualifiedName )
            // InternalProblemParser.g:1577:5: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getAnnotationRule());
              					}
              				
            }
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getAnnotationAccess().getDeclarationAnnotationDeclarationCrossReference_1_0());
              				
            }
            pushFollow(FOLLOW_37);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:1591:3: (otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==LeftParenthesis) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // InternalProblemParser.g:1592:4: otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )? otherlv_6= RightParenthesis
                    {
                    otherlv_2=(Token)match(input,LeftParenthesis,FOLLOW_38); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_2, grammarAccess.getAnnotationAccess().getLeftParenthesisKeyword_2_0());
                      			
                    }
                    // InternalProblemParser.g:1596:4: ( ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )* )?
                    int alt46=2;
                    int LA46_0 = input.LA(1);

                    if ( ((LA46_0>=Concretization && LA46_0<=Primitive)||(LA46_0>=Contains && LA46_0<=Opposite)||(LA46_0>=Partial && LA46_0<=Assert)||LA46_0==Module||LA46_0==Shadow||(LA46_0>=Error && LA46_0<=Multi)||LA46_0==Atom||LA46_0==Must||LA46_0==True||LA46_0==May||LA46_0==ColonColon||LA46_0==As||LA46_0==ExclamationMark||LA46_0==LeftParenthesis||(LA46_0>=Asterisk && LA46_0<=PlusSign)||LA46_0==HyphenMinus||(LA46_0>=RULE_ID && LA46_0<=RULE_EXPONENTIAL)||(LA46_0>=RULE_STRING && LA46_0<=RULE_QUOTED_ID)) ) {
                        alt46=1;
                    }
                    switch (alt46) {
                        case 1 :
                            // InternalProblemParser.g:1597:5: ( (lv_arguments_3_0= ruleAnnotationArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )*
                            {
                            // InternalProblemParser.g:1597:5: ( (lv_arguments_3_0= ruleAnnotationArgument ) )
                            // InternalProblemParser.g:1598:6: (lv_arguments_3_0= ruleAnnotationArgument )
                            {
                            // InternalProblemParser.g:1598:6: (lv_arguments_3_0= ruleAnnotationArgument )
                            // InternalProblemParser.g:1599:7: lv_arguments_3_0= ruleAnnotationArgument
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getAnnotationAccess().getArgumentsAnnotationArgumentParserRuleCall_2_1_0_0());
                              						
                            }
                            pushFollow(FOLLOW_23);
                            lv_arguments_3_0=ruleAnnotationArgument();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getAnnotationRule());
                              							}
                              							add(
                              								current,
                              								"arguments",
                              								lv_arguments_3_0,
                              								"tools.refinery.language.Problem.AnnotationArgument");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }

                            // InternalProblemParser.g:1616:5: (otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) ) )*
                            loop45:
                            do {
                                int alt45=2;
                                int LA45_0 = input.LA(1);

                                if ( (LA45_0==Comma) ) {
                                    alt45=1;
                                }


                                switch (alt45) {
                            	case 1 :
                            	    // InternalProblemParser.g:1617:6: otherlv_4= Comma ( (lv_arguments_5_0= ruleAnnotationArgument ) )
                            	    {
                            	    otherlv_4=(Token)match(input,Comma,FOLLOW_28); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      						newLeafNode(otherlv_4, grammarAccess.getAnnotationAccess().getCommaKeyword_2_1_1_0());
                            	      					
                            	    }
                            	    // InternalProblemParser.g:1621:6: ( (lv_arguments_5_0= ruleAnnotationArgument ) )
                            	    // InternalProblemParser.g:1622:7: (lv_arguments_5_0= ruleAnnotationArgument )
                            	    {
                            	    // InternalProblemParser.g:1622:7: (lv_arguments_5_0= ruleAnnotationArgument )
                            	    // InternalProblemParser.g:1623:8: lv_arguments_5_0= ruleAnnotationArgument
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      								newCompositeNode(grammarAccess.getAnnotationAccess().getArgumentsAnnotationArgumentParserRuleCall_2_1_1_1_0());
                            	      							
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_arguments_5_0=ruleAnnotationArgument();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      								if (current==null) {
                            	      									current = createModelElementForParent(grammarAccess.getAnnotationRule());
                            	      								}
                            	      								add(
                            	      									current,
                            	      									"arguments",
                            	      									lv_arguments_5_0,
                            	      									"tools.refinery.language.Problem.AnnotationArgument");
                            	      								afterParserOrEnumRuleCall();
                            	      							
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop45;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_6=(Token)match(input,RightParenthesis,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_6, grammarAccess.getAnnotationAccess().getRightParenthesisKeyword_2_2());
                      			
                    }

                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAnnotation"


    // $ANTLR start "entryRuleAnnotationArgument"
    // InternalProblemParser.g:1651:1: entryRuleAnnotationArgument returns [EObject current=null] : iv_ruleAnnotationArgument= ruleAnnotationArgument EOF ;
    public final EObject entryRuleAnnotationArgument() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAnnotationArgument = null;


        try {
            // InternalProblemParser.g:1651:59: (iv_ruleAnnotationArgument= ruleAnnotationArgument EOF )
            // InternalProblemParser.g:1652:2: iv_ruleAnnotationArgument= ruleAnnotationArgument EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAnnotationArgumentRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAnnotationArgument=ruleAnnotationArgument();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAnnotationArgument; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAnnotationArgument"


    // $ANTLR start "ruleAnnotationArgument"
    // InternalProblemParser.g:1658:1: ruleAnnotationArgument returns [EObject current=null] : ( () ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )? ( (lv_value_3_0= ruleExpr ) ) ) ;
    public final EObject ruleAnnotationArgument() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        EObject lv_value_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1664:2: ( ( () ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )? ( (lv_value_3_0= ruleExpr ) ) ) )
            // InternalProblemParser.g:1665:2: ( () ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )? ( (lv_value_3_0= ruleExpr ) ) )
            {
            // InternalProblemParser.g:1665:2: ( () ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )? ( (lv_value_3_0= ruleExpr ) ) )
            // InternalProblemParser.g:1666:3: () ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )? ( (lv_value_3_0= ruleExpr ) )
            {
            // InternalProblemParser.g:1666:3: ()
            // InternalProblemParser.g:1667:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getAnnotationArgumentAccess().getAnnotationArgumentAction_0(),
              					current);
              			
            }

            }

            // InternalProblemParser.g:1673:3: ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )?
            int alt48=2;
            alt48 = dfa48.predict(input);
            switch (alt48) {
                case 1 :
                    // InternalProblemParser.g:1674:4: ( ( ruleIdentifier ) ) otherlv_2= EqualsSign
                    {
                    // InternalProblemParser.g:1674:4: ( ( ruleIdentifier ) )
                    // InternalProblemParser.g:1675:5: ( ruleIdentifier )
                    {
                    // InternalProblemParser.g:1675:5: ( ruleIdentifier )
                    // InternalProblemParser.g:1676:6: ruleIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getAnnotationArgumentRule());
                      						}
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAnnotationArgumentAccess().getParameterParameterCrossReference_1_0_0());
                      					
                    }
                    pushFollow(FOLLOW_39);
                    ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    otherlv_2=(Token)match(input,EqualsSign,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_2, grammarAccess.getAnnotationArgumentAccess().getEqualsSignKeyword_1_1());
                      			
                    }

                    }
                    break;

            }

            // InternalProblemParser.g:1695:3: ( (lv_value_3_0= ruleExpr ) )
            // InternalProblemParser.g:1696:4: (lv_value_3_0= ruleExpr )
            {
            // InternalProblemParser.g:1696:4: (lv_value_3_0= ruleExpr )
            // InternalProblemParser.g:1697:5: lv_value_3_0= ruleExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getAnnotationArgumentAccess().getValueExprParserRuleCall_2_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_value_3_0=ruleExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getAnnotationArgumentRule());
              					}
              					set(
              						current,
              						"value",
              						lv_value_3_0,
              						"tools.refinery.language.Problem.Expr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAnnotationArgument"


    // $ANTLR start "entryRuleImportStatement"
    // InternalProblemParser.g:1718:1: entryRuleImportStatement returns [EObject current=null] : iv_ruleImportStatement= ruleImportStatement EOF ;
    public final EObject entryRuleImportStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleImportStatement = null;


        try {
            // InternalProblemParser.g:1718:56: (iv_ruleImportStatement= ruleImportStatement EOF )
            // InternalProblemParser.g:1719:2: iv_ruleImportStatement= ruleImportStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getImportStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleImportStatement=ruleImportStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleImportStatement; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleImportStatement"


    // $ANTLR start "ruleImportStatement"
    // InternalProblemParser.g:1725:1: ruleImportStatement returns [EObject current=null] : (otherlv_0= Import ( ( ruleQualifiedName ) ) (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )? otherlv_4= FullStop ) ;
    public final EObject ruleImportStatement() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        Token lv_alias_3_0=null;
        Token otherlv_4=null;


        	enterRule();

        try {
            // InternalProblemParser.g:1731:2: ( (otherlv_0= Import ( ( ruleQualifiedName ) ) (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )? otherlv_4= FullStop ) )
            // InternalProblemParser.g:1732:2: (otherlv_0= Import ( ( ruleQualifiedName ) ) (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )? otherlv_4= FullStop )
            {
            // InternalProblemParser.g:1732:2: (otherlv_0= Import ( ( ruleQualifiedName ) ) (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )? otherlv_4= FullStop )
            // InternalProblemParser.g:1733:3: otherlv_0= Import ( ( ruleQualifiedName ) ) (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )? otherlv_4= FullStop
            {
            otherlv_0=(Token)match(input,Import,FOLLOW_8); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getImportStatementAccess().getImportKeyword_0());
              		
            }
            // InternalProblemParser.g:1737:3: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:1738:4: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:1738:4: ( ruleQualifiedName )
            // InternalProblemParser.g:1739:5: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getImportStatementRule());
              					}
              				
            }
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getImportStatementAccess().getImportedModuleProblemCrossReference_1_0());
              				
            }
            pushFollow(FOLLOW_40);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:1753:3: (otherlv_2= As ( (lv_alias_3_0= RULE_ID ) ) )?
            int alt49=2;
            int LA49_0 = input.LA(1);

            if ( (LA49_0==As) ) {
                alt49=1;
            }
            switch (alt49) {
                case 1 :
                    // InternalProblemParser.g:1754:4: otherlv_2= As ( (lv_alias_3_0= RULE_ID ) )
                    {
                    otherlv_2=(Token)match(input,As,FOLLOW_41); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_2, grammarAccess.getImportStatementAccess().getAsKeyword_2_0());
                      			
                    }
                    // InternalProblemParser.g:1758:4: ( (lv_alias_3_0= RULE_ID ) )
                    // InternalProblemParser.g:1759:5: (lv_alias_3_0= RULE_ID )
                    {
                    // InternalProblemParser.g:1759:5: (lv_alias_3_0= RULE_ID )
                    // InternalProblemParser.g:1760:6: lv_alias_3_0= RULE_ID
                    {
                    lv_alias_3_0=(Token)match(input,RULE_ID,FOLLOW_4); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						newLeafNode(lv_alias_3_0, grammarAccess.getImportStatementAccess().getAliasIDTerminalRuleCall_2_1_0());
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getImportStatementRule());
                      						}
                      						setWithLastConsumed(
                      							current,
                      							"alias",
                      							lv_alias_3_0,
                      							"tools.refinery.language.Problem.ID");
                      					
                    }

                    }


                    }


                    }
                    break;

            }

            otherlv_4=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_4, grammarAccess.getImportStatementAccess().getFullStopKeyword_3());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleImportStatement"


    // $ANTLR start "entryRuleEnumLiteral"
    // InternalProblemParser.g:1785:1: entryRuleEnumLiteral returns [EObject current=null] : iv_ruleEnumLiteral= ruleEnumLiteral EOF ;
    public final EObject entryRuleEnumLiteral() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleEnumLiteral = null;


        try {
            // InternalProblemParser.g:1785:52: (iv_ruleEnumLiteral= ruleEnumLiteral EOF )
            // InternalProblemParser.g:1786:2: iv_ruleEnumLiteral= ruleEnumLiteral EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getEnumLiteralRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleEnumLiteral=ruleEnumLiteral();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleEnumLiteral; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleEnumLiteral"


    // $ANTLR start "ruleEnumLiteral"
    // InternalProblemParser.g:1792:1: ruleEnumLiteral returns [EObject current=null] : ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( (lv_name_1_0= ruleIdentifier ) ) ) ;
    public final EObject ruleEnumLiteral() throws RecognitionException {
        EObject current = null;

        EObject lv_annotations_0_0 = null;

        AntlrDatatypeRuleToken lv_name_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1798:2: ( ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( (lv_name_1_0= ruleIdentifier ) ) ) )
            // InternalProblemParser.g:1799:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( (lv_name_1_0= ruleIdentifier ) ) )
            {
            // InternalProblemParser.g:1799:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( (lv_name_1_0= ruleIdentifier ) ) )
            // InternalProblemParser.g:1800:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( (lv_name_1_0= ruleIdentifier ) )
            {
            // InternalProblemParser.g:1800:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) )
            // InternalProblemParser.g:1801:4: (lv_annotations_0_0= ruleAnnotationContainer )
            {
            // InternalProblemParser.g:1801:4: (lv_annotations_0_0= ruleAnnotationContainer )
            // InternalProblemParser.g:1802:5: lv_annotations_0_0= ruleAnnotationContainer
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getEnumLiteralAccess().getAnnotationsAnnotationContainerParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_8);
            lv_annotations_0_0=ruleAnnotationContainer();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getEnumLiteralRule());
              					}
              					set(
              						current,
              						"annotations",
              						lv_annotations_0_0,
              						"tools.refinery.language.Problem.AnnotationContainer");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:1819:3: ( (lv_name_1_0= ruleIdentifier ) )
            // InternalProblemParser.g:1820:4: (lv_name_1_0= ruleIdentifier )
            {
            // InternalProblemParser.g:1820:4: (lv_name_1_0= ruleIdentifier )
            // InternalProblemParser.g:1821:5: lv_name_1_0= ruleIdentifier
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getEnumLiteralAccess().getNameIdentifierParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_name_1_0=ruleIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getEnumLiteralRule());
              					}
              					set(
              						current,
              						"name",
              						lv_name_1_0,
              						"tools.refinery.language.Problem.Identifier");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleEnumLiteral"


    // $ANTLR start "entryRuleReferenceDeclaration"
    // InternalProblemParser.g:1842:1: entryRuleReferenceDeclaration returns [EObject current=null] : iv_ruleReferenceDeclaration= ruleReferenceDeclaration EOF ;
    public final EObject entryRuleReferenceDeclaration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleReferenceDeclaration = null;


        try {
            // InternalProblemParser.g:1842:61: (iv_ruleReferenceDeclaration= ruleReferenceDeclaration EOF )
            // InternalProblemParser.g:1843:2: iv_ruleReferenceDeclaration= ruleReferenceDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getReferenceDeclarationRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleReferenceDeclaration=ruleReferenceDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleReferenceDeclaration; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleReferenceDeclaration"


    // $ANTLR start "ruleReferenceDeclaration"
    // InternalProblemParser.g:1849:1: ruleReferenceDeclaration returns [EObject current=null] : ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) ) ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )? ( (lv_name_5_0= ruleIdentifier ) ) ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) ) ) ;
    public final EObject ruleReferenceDeclaration() throws RecognitionException {
        EObject current = null;

        Token otherlv_7=null;
        Token otherlv_9=null;
        Token otherlv_11=null;
        EObject lv_annotations_0_0 = null;

        Enumerator lv_kind_2_0 = null;

        EObject lv_multiplicity_4_0 = null;

        AntlrDatatypeRuleToken lv_name_5_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:1855:2: ( ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) ) ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )? ( (lv_name_5_0= ruleIdentifier ) ) ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) ) ) )
            // InternalProblemParser.g:1856:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) ) ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )? ( (lv_name_5_0= ruleIdentifier ) ) ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) ) )
            {
            // InternalProblemParser.g:1856:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) ) ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )? ( (lv_name_5_0= ruleIdentifier ) ) ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) ) )
            // InternalProblemParser.g:1857:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) ) ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )? ( (lv_name_5_0= ruleIdentifier ) ) ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) )
            {
            // InternalProblemParser.g:1857:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) )
            // InternalProblemParser.g:1858:4: (lv_annotations_0_0= ruleAnnotationContainer )
            {
            // InternalProblemParser.g:1858:4: (lv_annotations_0_0= ruleAnnotationContainer )
            // InternalProblemParser.g:1859:5: lv_annotations_0_0= ruleAnnotationContainer
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getAnnotationsAnnotationContainerParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_42);
            lv_annotations_0_0=ruleAnnotationContainer();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getReferenceDeclarationRule());
              					}
              					set(
              						current,
              						"annotations",
              						lv_annotations_0_0,
              						"tools.refinery.language.Problem.AnnotationContainer");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:1876:3: ( ( ( ruleNonContainmentQualifiedName ) ) | ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) ) )
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( ((LA50_0>=Concretization && LA50_0<=Aggregator)||LA50_0==Primitive||(LA50_0>=Datatype && LA50_0<=Decision)||LA50_0==Problem||LA50_0==Assert||LA50_0==Module||LA50_0==Shadow||LA50_0==Multi||LA50_0==Atom||LA50_0==ColonColon||LA50_0==As||LA50_0==RULE_ID||LA50_0==RULE_QUOTED_ID) ) {
                alt50=1;
            }
            else if ( (LA50_0==Container||LA50_0==Contains||LA50_0==Refers) ) {
                alt50=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 50, 0, input);

                throw nvae;
            }
            switch (alt50) {
                case 1 :
                    // InternalProblemParser.g:1877:4: ( ( ruleNonContainmentQualifiedName ) )
                    {
                    // InternalProblemParser.g:1877:4: ( ( ruleNonContainmentQualifiedName ) )
                    // InternalProblemParser.g:1878:5: ( ruleNonContainmentQualifiedName )
                    {
                    // InternalProblemParser.g:1878:5: ( ruleNonContainmentQualifiedName )
                    // InternalProblemParser.g:1879:6: ruleNonContainmentQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getReferenceDeclarationRule());
                      						}
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getReferenceTypeRelationCrossReference_1_0_0());
                      					
                    }
                    pushFollow(FOLLOW_43);
                    ruleNonContainmentQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:1894:4: ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) )
                    {
                    // InternalProblemParser.g:1894:4: ( ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) ) )
                    // InternalProblemParser.g:1895:5: ( (lv_kind_2_0= ruleReferenceKind ) ) ( ( ruleQualifiedName ) )
                    {
                    // InternalProblemParser.g:1895:5: ( (lv_kind_2_0= ruleReferenceKind ) )
                    // InternalProblemParser.g:1896:6: (lv_kind_2_0= ruleReferenceKind )
                    {
                    // InternalProblemParser.g:1896:6: (lv_kind_2_0= ruleReferenceKind )
                    // InternalProblemParser.g:1897:7: lv_kind_2_0= ruleReferenceKind
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getKindReferenceKindEnumRuleCall_1_1_0_0());
                      						
                    }
                    pushFollow(FOLLOW_8);
                    lv_kind_2_0=ruleReferenceKind();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getReferenceDeclarationRule());
                      							}
                      							set(
                      								current,
                      								"kind",
                      								lv_kind_2_0,
                      								"tools.refinery.language.Problem.ReferenceKind");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:1914:5: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:1915:6: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:1915:6: ( ruleQualifiedName )
                    // InternalProblemParser.g:1916:7: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElement(grammarAccess.getReferenceDeclarationRule());
                      							}
                      						
                    }
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getReferenceTypeRelationCrossReference_1_1_1_0());
                      						
                    }
                    pushFollow(FOLLOW_43);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }


                    }


                    }
                    break;

            }

            // InternalProblemParser.g:1932:3: ( (lv_multiplicity_4_0= ruleReferenceMultiplicity ) )?
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==LeftSquareBracket) ) {
                alt51=1;
            }
            switch (alt51) {
                case 1 :
                    // InternalProblemParser.g:1933:4: (lv_multiplicity_4_0= ruleReferenceMultiplicity )
                    {
                    // InternalProblemParser.g:1933:4: (lv_multiplicity_4_0= ruleReferenceMultiplicity )
                    // InternalProblemParser.g:1934:5: lv_multiplicity_4_0= ruleReferenceMultiplicity
                    {
                    if ( state.backtracking==0 ) {

                      					newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getMultiplicityReferenceMultiplicityParserRuleCall_2_0());
                      				
                    }
                    pushFollow(FOLLOW_8);
                    lv_multiplicity_4_0=ruleReferenceMultiplicity();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					if (current==null) {
                      						current = createModelElementForParent(grammarAccess.getReferenceDeclarationRule());
                      					}
                      					set(
                      						current,
                      						"multiplicity",
                      						lv_multiplicity_4_0,
                      						"tools.refinery.language.Problem.ReferenceMultiplicity");
                      					afterParserOrEnumRuleCall();
                      				
                    }

                    }


                    }
                    break;

            }

            // InternalProblemParser.g:1951:3: ( (lv_name_5_0= ruleIdentifier ) )
            // InternalProblemParser.g:1952:4: (lv_name_5_0= ruleIdentifier )
            {
            // InternalProblemParser.g:1952:4: (lv_name_5_0= ruleIdentifier )
            // InternalProblemParser.g:1953:5: lv_name_5_0= ruleIdentifier
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getNameIdentifierParserRuleCall_3_0());
              				
            }
            pushFollow(FOLLOW_44);
            lv_name_5_0=ruleIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getReferenceDeclarationRule());
              					}
              					set(
              						current,
              						"name",
              						lv_name_5_0,
              						"tools.refinery.language.Problem.Identifier");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:1970:3: ( ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) ) )
            // InternalProblemParser.g:1971:4: ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) )
            {
            // InternalProblemParser.g:1971:4: ( ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* ) )
            // InternalProblemParser.g:1972:5: ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* )
            {
            getUnorderedGroupHelper().enter(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4());
            // InternalProblemParser.g:1975:5: ( ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )* )
            // InternalProblemParser.g:1976:6: ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )*
            {
            // InternalProblemParser.g:1976:6: ( ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) ) | ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) ) )*
            loop53:
            do {
                int alt53=3;
                int LA53_0 = input.LA(1);

                if ( LA53_0 == Opposite && getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 0) ) {
                    alt53=1;
                }
                else if ( LA53_0 == Subsets && getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 1) ) {
                    alt53=2;
                }


                switch (alt53) {
            	case 1 :
            	    // InternalProblemParser.g:1977:4: ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) )
            	    {
            	    // InternalProblemParser.g:1977:4: ({...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) ) )
            	    // InternalProblemParser.g:1978:5: {...}? => ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) )
            	    {
            	    if ( ! getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 0) ) {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        throw new FailedPredicateException(input, "ruleReferenceDeclaration", "getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 0)");
            	    }
            	    // InternalProblemParser.g:1978:117: ( ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) ) )
            	    // InternalProblemParser.g:1979:6: ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) )
            	    {
            	    getUnorderedGroupHelper().select(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 0);
            	    // InternalProblemParser.g:1982:9: ({...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) ) )
            	    // InternalProblemParser.g:1982:10: {...}? => (otherlv_7= Opposite ( ( ruleQualifiedName ) ) )
            	    {
            	    if ( !((true)) ) {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        throw new FailedPredicateException(input, "ruleReferenceDeclaration", "true");
            	    }
            	    // InternalProblemParser.g:1982:19: (otherlv_7= Opposite ( ( ruleQualifiedName ) ) )
            	    // InternalProblemParser.g:1982:20: otherlv_7= Opposite ( ( ruleQualifiedName ) )
            	    {
            	    otherlv_7=(Token)match(input,Opposite,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      									newLeafNode(otherlv_7, grammarAccess.getReferenceDeclarationAccess().getOppositeKeyword_4_0_0());
            	      								
            	    }
            	    // InternalProblemParser.g:1986:9: ( ( ruleQualifiedName ) )
            	    // InternalProblemParser.g:1987:10: ( ruleQualifiedName )
            	    {
            	    // InternalProblemParser.g:1987:10: ( ruleQualifiedName )
            	    // InternalProblemParser.g:1988:11: ruleQualifiedName
            	    {
            	    if ( state.backtracking==0 ) {

            	      											if (current==null) {
            	      												current = createModelElement(grammarAccess.getReferenceDeclarationRule());
            	      											}
            	      										
            	    }
            	    if ( state.backtracking==0 ) {

            	      											newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getOppositeReferenceDeclarationCrossReference_4_0_1_0());
            	      										
            	    }
            	    pushFollow(FOLLOW_44);
            	    ruleQualifiedName();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      											afterParserOrEnumRuleCall();
            	      										
            	    }

            	    }


            	    }


            	    }


            	    }

            	    getUnorderedGroupHelper().returnFromSelection(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4());

            	    }


            	    }


            	    }
            	    break;
            	case 2 :
            	    // InternalProblemParser.g:2008:4: ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) )
            	    {
            	    // InternalProblemParser.g:2008:4: ({...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) ) )
            	    // InternalProblemParser.g:2009:5: {...}? => ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) )
            	    {
            	    if ( ! getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 1) ) {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        throw new FailedPredicateException(input, "ruleReferenceDeclaration", "getUnorderedGroupHelper().canSelect(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 1)");
            	    }
            	    // InternalProblemParser.g:2009:117: ( ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) ) )
            	    // InternalProblemParser.g:2010:6: ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) )
            	    {
            	    getUnorderedGroupHelper().select(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4(), 1);
            	    // InternalProblemParser.g:2013:9: ({...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* ) )
            	    // InternalProblemParser.g:2013:10: {...}? => (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* )
            	    {
            	    if ( !((true)) ) {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        throw new FailedPredicateException(input, "ruleReferenceDeclaration", "true");
            	    }
            	    // InternalProblemParser.g:2013:19: (otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )* )
            	    // InternalProblemParser.g:2013:20: otherlv_9= Subsets ( ( ruleQualifiedName ) ) (otherlv_11= Comma ( ( ruleQualifiedName ) ) )*
            	    {
            	    otherlv_9=(Token)match(input,Subsets,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      									newLeafNode(otherlv_9, grammarAccess.getReferenceDeclarationAccess().getSubsetsKeyword_4_1_0());
            	      								
            	    }
            	    // InternalProblemParser.g:2017:9: ( ( ruleQualifiedName ) )
            	    // InternalProblemParser.g:2018:10: ( ruleQualifiedName )
            	    {
            	    // InternalProblemParser.g:2018:10: ( ruleQualifiedName )
            	    // InternalProblemParser.g:2019:11: ruleQualifiedName
            	    {
            	    if ( state.backtracking==0 ) {

            	      											if (current==null) {
            	      												current = createModelElement(grammarAccess.getReferenceDeclarationRule());
            	      											}
            	      										
            	    }
            	    if ( state.backtracking==0 ) {

            	      											newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getSuperSetsReferenceDeclarationCrossReference_4_1_1_0());
            	      										
            	    }
            	    pushFollow(FOLLOW_45);
            	    ruleQualifiedName();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      											afterParserOrEnumRuleCall();
            	      										
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:2033:9: (otherlv_11= Comma ( ( ruleQualifiedName ) ) )*
            	    loop52:
            	    do {
            	        int alt52=2;
            	        int LA52_0 = input.LA(1);

            	        if ( (LA52_0==Comma) ) {
            	            alt52=1;
            	        }


            	        switch (alt52) {
            	    	case 1 :
            	    	    // InternalProblemParser.g:2034:10: otherlv_11= Comma ( ( ruleQualifiedName ) )
            	    	    {
            	    	    otherlv_11=(Token)match(input,Comma,FOLLOW_8); if (state.failed) return current;
            	    	    if ( state.backtracking==0 ) {

            	    	      										newLeafNode(otherlv_11, grammarAccess.getReferenceDeclarationAccess().getCommaKeyword_4_1_2_0());
            	    	      									
            	    	    }
            	    	    // InternalProblemParser.g:2038:10: ( ( ruleQualifiedName ) )
            	    	    // InternalProblemParser.g:2039:11: ( ruleQualifiedName )
            	    	    {
            	    	    // InternalProblemParser.g:2039:11: ( ruleQualifiedName )
            	    	    // InternalProblemParser.g:2040:12: ruleQualifiedName
            	    	    {
            	    	    if ( state.backtracking==0 ) {

            	    	      												if (current==null) {
            	    	      													current = createModelElement(grammarAccess.getReferenceDeclarationRule());
            	    	      												}
            	    	      											
            	    	    }
            	    	    if ( state.backtracking==0 ) {

            	    	      												newCompositeNode(grammarAccess.getReferenceDeclarationAccess().getSuperSetsReferenceDeclarationCrossReference_4_1_2_1_0());
            	    	      											
            	    	    }
            	    	    pushFollow(FOLLOW_45);
            	    	    ruleQualifiedName();

            	    	    state._fsp--;
            	    	    if (state.failed) return current;
            	    	    if ( state.backtracking==0 ) {

            	    	      												afterParserOrEnumRuleCall();
            	    	      											
            	    	    }

            	    	    }


            	    	    }


            	    	    }
            	    	    break;

            	    	default :
            	    	    break loop52;
            	        }
            	    } while (true);


            	    }


            	    }

            	    getUnorderedGroupHelper().returnFromSelection(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4());

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop53;
                }
            } while (true);


            }


            }

            getUnorderedGroupHelper().leave(grammarAccess.getReferenceDeclarationAccess().getUnorderedGroup_4());

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleReferenceDeclaration"


    // $ANTLR start "entryRuleReferenceMultiplicity"
    // InternalProblemParser.g:2072:1: entryRuleReferenceMultiplicity returns [EObject current=null] : iv_ruleReferenceMultiplicity= ruleReferenceMultiplicity EOF ;
    public final EObject entryRuleReferenceMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleReferenceMultiplicity = null;


        try {
            // InternalProblemParser.g:2072:62: (iv_ruleReferenceMultiplicity= ruleReferenceMultiplicity EOF )
            // InternalProblemParser.g:2073:2: iv_ruleReferenceMultiplicity= ruleReferenceMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getReferenceMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleReferenceMultiplicity=ruleReferenceMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleReferenceMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleReferenceMultiplicity"


    // $ANTLR start "ruleReferenceMultiplicity"
    // InternalProblemParser.g:2079:1: ruleReferenceMultiplicity returns [EObject current=null] : (otherlv_0= LeftSquareBracket this_Multiplicity_1= ruleMultiplicity otherlv_2= RightSquareBracket ) ;
    public final EObject ruleReferenceMultiplicity() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        EObject this_Multiplicity_1 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2085:2: ( (otherlv_0= LeftSquareBracket this_Multiplicity_1= ruleMultiplicity otherlv_2= RightSquareBracket ) )
            // InternalProblemParser.g:2086:2: (otherlv_0= LeftSquareBracket this_Multiplicity_1= ruleMultiplicity otherlv_2= RightSquareBracket )
            {
            // InternalProblemParser.g:2086:2: (otherlv_0= LeftSquareBracket this_Multiplicity_1= ruleMultiplicity otherlv_2= RightSquareBracket )
            // InternalProblemParser.g:2087:3: otherlv_0= LeftSquareBracket this_Multiplicity_1= ruleMultiplicity otherlv_2= RightSquareBracket
            {
            otherlv_0=(Token)match(input,LeftSquareBracket,FOLLOW_46); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getReferenceMultiplicityAccess().getLeftSquareBracketKeyword_0());
              		
            }
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getReferenceMultiplicityAccess().getMultiplicityParserRuleCall_1());
              		
            }
            pushFollow(FOLLOW_47);
            this_Multiplicity_1=ruleMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_Multiplicity_1;
              			afterParserOrEnumRuleCall();
              		
            }
            otherlv_2=(Token)match(input,RightSquareBracket,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_2, grammarAccess.getReferenceMultiplicityAccess().getRightSquareBracketKeyword_2());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleReferenceMultiplicity"


    // $ANTLR start "entryRuleConjunction"
    // InternalProblemParser.g:2107:1: entryRuleConjunction returns [EObject current=null] : iv_ruleConjunction= ruleConjunction EOF ;
    public final EObject entryRuleConjunction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConjunction = null;


        try {
            // InternalProblemParser.g:2107:52: (iv_ruleConjunction= ruleConjunction EOF )
            // InternalProblemParser.g:2108:2: iv_ruleConjunction= ruleConjunction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConjunctionRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleConjunction=ruleConjunction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConjunction; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleConjunction"


    // $ANTLR start "ruleConjunction"
    // InternalProblemParser.g:2114:1: ruleConjunction returns [EObject current=null] : ( ( (lv_literals_0_0= ruleExpr ) ) (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )* ) ;
    public final EObject ruleConjunction() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        EObject lv_literals_0_0 = null;

        EObject lv_literals_2_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2120:2: ( ( ( (lv_literals_0_0= ruleExpr ) ) (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )* ) )
            // InternalProblemParser.g:2121:2: ( ( (lv_literals_0_0= ruleExpr ) ) (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )* )
            {
            // InternalProblemParser.g:2121:2: ( ( (lv_literals_0_0= ruleExpr ) ) (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )* )
            // InternalProblemParser.g:2122:3: ( (lv_literals_0_0= ruleExpr ) ) (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )*
            {
            // InternalProblemParser.g:2122:3: ( (lv_literals_0_0= ruleExpr ) )
            // InternalProblemParser.g:2123:4: (lv_literals_0_0= ruleExpr )
            {
            // InternalProblemParser.g:2123:4: (lv_literals_0_0= ruleExpr )
            // InternalProblemParser.g:2124:5: lv_literals_0_0= ruleExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getConjunctionAccess().getLiteralsExprParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_48);
            lv_literals_0_0=ruleExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getConjunctionRule());
              					}
              					add(
              						current,
              						"literals",
              						lv_literals_0_0,
              						"tools.refinery.language.Problem.Expr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:2141:3: (otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) ) )*
            loop54:
            do {
                int alt54=2;
                int LA54_0 = input.LA(1);

                if ( (LA54_0==Comma) ) {
                    alt54=1;
                }


                switch (alt54) {
            	case 1 :
            	    // InternalProblemParser.g:2142:4: otherlv_1= Comma ( (lv_literals_2_0= ruleExpr ) )
            	    {
            	    otherlv_1=(Token)match(input,Comma,FOLLOW_28); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_1, grammarAccess.getConjunctionAccess().getCommaKeyword_1_0());
            	      			
            	    }
            	    // InternalProblemParser.g:2146:4: ( (lv_literals_2_0= ruleExpr ) )
            	    // InternalProblemParser.g:2147:5: (lv_literals_2_0= ruleExpr )
            	    {
            	    // InternalProblemParser.g:2147:5: (lv_literals_2_0= ruleExpr )
            	    // InternalProblemParser.g:2148:6: lv_literals_2_0= ruleExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getConjunctionAccess().getLiteralsExprParserRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_48);
            	    lv_literals_2_0=ruleExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getConjunctionRule());
            	      						}
            	      						add(
            	      							current,
            	      							"literals",
            	      							lv_literals_2_0,
            	      							"tools.refinery.language.Problem.Expr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop54;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleConjunction"


    // $ANTLR start "entryRuleCase"
    // InternalProblemParser.g:2170:1: entryRuleCase returns [EObject current=null] : iv_ruleCase= ruleCase EOF ;
    public final EObject entryRuleCase() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleCase = null;


        try {
            // InternalProblemParser.g:2170:45: (iv_ruleCase= ruleCase EOF )
            // InternalProblemParser.g:2171:2: iv_ruleCase= ruleCase EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getCaseRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleCase=ruleCase();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleCase; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleCase"


    // $ANTLR start "ruleCase"
    // InternalProblemParser.g:2177:1: ruleCase returns [EObject current=null] : ( ( (lv_condition_0_0= ruleConjunction ) ) (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )? ) ;
    public final EObject ruleCase() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        EObject lv_condition_0_0 = null;

        EObject lv_value_2_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2183:2: ( ( ( (lv_condition_0_0= ruleConjunction ) ) (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )? ) )
            // InternalProblemParser.g:2184:2: ( ( (lv_condition_0_0= ruleConjunction ) ) (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )? )
            {
            // InternalProblemParser.g:2184:2: ( ( (lv_condition_0_0= ruleConjunction ) ) (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )? )
            // InternalProblemParser.g:2185:3: ( (lv_condition_0_0= ruleConjunction ) ) (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )?
            {
            // InternalProblemParser.g:2185:3: ( (lv_condition_0_0= ruleConjunction ) )
            // InternalProblemParser.g:2186:4: (lv_condition_0_0= ruleConjunction )
            {
            // InternalProblemParser.g:2186:4: (lv_condition_0_0= ruleConjunction )
            // InternalProblemParser.g:2187:5: lv_condition_0_0= ruleConjunction
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getCaseAccess().getConditionConjunctionParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_49);
            lv_condition_0_0=ruleConjunction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getCaseRule());
              					}
              					set(
              						current,
              						"condition",
              						lv_condition_0_0,
              						"tools.refinery.language.Problem.Conjunction");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:2204:3: (otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) ) )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( (LA55_0==HyphenMinusGreaterThanSign) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // InternalProblemParser.g:2205:4: otherlv_1= HyphenMinusGreaterThanSign ( (lv_value_2_0= ruleExpr ) )
                    {
                    otherlv_1=(Token)match(input,HyphenMinusGreaterThanSign,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_1, grammarAccess.getCaseAccess().getHyphenMinusGreaterThanSignKeyword_1_0());
                      			
                    }
                    // InternalProblemParser.g:2209:4: ( (lv_value_2_0= ruleExpr ) )
                    // InternalProblemParser.g:2210:5: (lv_value_2_0= ruleExpr )
                    {
                    // InternalProblemParser.g:2210:5: (lv_value_2_0= ruleExpr )
                    // InternalProblemParser.g:2211:6: lv_value_2_0= ruleExpr
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getCaseAccess().getValueExprParserRuleCall_1_1_0());
                      					
                    }
                    pushFollow(FOLLOW_2);
                    lv_value_2_0=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getCaseRule());
                      						}
                      						set(
                      							current,
                      							"value",
                      							lv_value_2_0,
                      							"tools.refinery.language.Problem.Expr");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleCase"


    // $ANTLR start "entryRuleParameter"
    // InternalProblemParser.g:2233:1: entryRuleParameter returns [EObject current=null] : iv_ruleParameter= ruleParameter EOF ;
    public final EObject entryRuleParameter() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleParameter = null;


        try {
            // InternalProblemParser.g:2233:50: (iv_ruleParameter= ruleParameter EOF )
            // InternalProblemParser.g:2234:2: iv_ruleParameter= ruleParameter EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getParameterRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleParameter=ruleParameter();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleParameter; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleParameter"


    // $ANTLR start "ruleParameter"
    // InternalProblemParser.g:2240:1: ruleParameter returns [EObject current=null] : ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )? ( (lv_name_3_0= ruleIdentifier ) ) ) ;
    public final EObject ruleParameter() throws RecognitionException {
        EObject current = null;

        EObject lv_annotations_0_0 = null;

        Enumerator lv_kind_1_0 = null;

        AntlrDatatypeRuleToken lv_name_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2246:2: ( ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )? ( (lv_name_3_0= ruleIdentifier ) ) ) )
            // InternalProblemParser.g:2247:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )? ( (lv_name_3_0= ruleIdentifier ) ) )
            {
            // InternalProblemParser.g:2247:2: ( ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )? ( (lv_name_3_0= ruleIdentifier ) ) )
            // InternalProblemParser.g:2248:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) ) ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )? ( (lv_name_3_0= ruleIdentifier ) )
            {
            // InternalProblemParser.g:2248:3: ( (lv_annotations_0_0= ruleAnnotationContainer ) )
            // InternalProblemParser.g:2249:4: (lv_annotations_0_0= ruleAnnotationContainer )
            {
            // InternalProblemParser.g:2249:4: (lv_annotations_0_0= ruleAnnotationContainer )
            // InternalProblemParser.g:2250:5: lv_annotations_0_0= ruleAnnotationContainer
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getParameterAccess().getAnnotationsAnnotationContainerParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_50);
            lv_annotations_0_0=ruleAnnotationContainer();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getParameterRule());
              					}
              					set(
              						current,
              						"annotations",
              						lv_annotations_0_0,
              						"tools.refinery.language.Problem.AnnotationContainer");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:2267:3: ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )?
            int alt56=3;
            alt56 = dfa56.predict(input);
            switch (alt56) {
                case 1 :
                    // InternalProblemParser.g:2268:4: ( (lv_kind_1_0= ruleParameterKind ) )
                    {
                    // InternalProblemParser.g:2268:4: ( (lv_kind_1_0= ruleParameterKind ) )
                    // InternalProblemParser.g:2269:5: (lv_kind_1_0= ruleParameterKind )
                    {
                    // InternalProblemParser.g:2269:5: (lv_kind_1_0= ruleParameterKind )
                    // InternalProblemParser.g:2270:6: lv_kind_1_0= ruleParameterKind
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getParameterAccess().getKindParameterKindEnumRuleCall_1_0_0());
                      					
                    }
                    pushFollow(FOLLOW_8);
                    lv_kind_1_0=ruleParameterKind();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getParameterRule());
                      						}
                      						set(
                      							current,
                      							"kind",
                      							lv_kind_1_0,
                      							"tools.refinery.language.Problem.ParameterKind");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:2288:4: ( ( ruleQualifiedName ) )
                    {
                    // InternalProblemParser.g:2288:4: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:2289:5: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:2289:5: ( ruleQualifiedName )
                    // InternalProblemParser.g:2290:6: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getParameterRule());
                      						}
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getParameterAccess().getParameterTypeRelationCrossReference_1_1_0());
                      					
                    }
                    pushFollow(FOLLOW_8);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;

            }

            // InternalProblemParser.g:2305:3: ( (lv_name_3_0= ruleIdentifier ) )
            // InternalProblemParser.g:2306:4: (lv_name_3_0= ruleIdentifier )
            {
            // InternalProblemParser.g:2306:4: (lv_name_3_0= ruleIdentifier )
            // InternalProblemParser.g:2307:5: lv_name_3_0= ruleIdentifier
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getParameterAccess().getNameIdentifierParserRuleCall_2_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_name_3_0=ruleIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getParameterRule());
              					}
              					set(
              						current,
              						"name",
              						lv_name_3_0,
              						"tools.refinery.language.Problem.Identifier");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleParameter"


    // $ANTLR start "entryRuleConsequent"
    // InternalProblemParser.g:2328:1: entryRuleConsequent returns [EObject current=null] : iv_ruleConsequent= ruleConsequent EOF ;
    public final EObject entryRuleConsequent() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConsequent = null;


        try {
            // InternalProblemParser.g:2328:51: (iv_ruleConsequent= ruleConsequent EOF )
            // InternalProblemParser.g:2329:2: iv_ruleConsequent= ruleConsequent EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConsequentRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleConsequent=ruleConsequent();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConsequent; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleConsequent"


    // $ANTLR start "ruleConsequent"
    // InternalProblemParser.g:2335:1: ruleConsequent returns [EObject current=null] : ( ( (lv_actions_0_0= ruleAction ) ) (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )* ) ;
    public final EObject ruleConsequent() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        EObject lv_actions_0_0 = null;

        EObject lv_actions_2_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2341:2: ( ( ( (lv_actions_0_0= ruleAction ) ) (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )* ) )
            // InternalProblemParser.g:2342:2: ( ( (lv_actions_0_0= ruleAction ) ) (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )* )
            {
            // InternalProblemParser.g:2342:2: ( ( (lv_actions_0_0= ruleAction ) ) (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )* )
            // InternalProblemParser.g:2343:3: ( (lv_actions_0_0= ruleAction ) ) (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )*
            {
            // InternalProblemParser.g:2343:3: ( (lv_actions_0_0= ruleAction ) )
            // InternalProblemParser.g:2344:4: (lv_actions_0_0= ruleAction )
            {
            // InternalProblemParser.g:2344:4: (lv_actions_0_0= ruleAction )
            // InternalProblemParser.g:2345:5: lv_actions_0_0= ruleAction
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getConsequentAccess().getActionsActionParserRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_48);
            lv_actions_0_0=ruleAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getConsequentRule());
              					}
              					add(
              						current,
              						"actions",
              						lv_actions_0_0,
              						"tools.refinery.language.Problem.Action");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:2362:3: (otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) ) )*
            loop57:
            do {
                int alt57=2;
                int LA57_0 = input.LA(1);

                if ( (LA57_0==Comma) ) {
                    alt57=1;
                }


                switch (alt57) {
            	case 1 :
            	    // InternalProblemParser.g:2363:4: otherlv_1= Comma ( (lv_actions_2_0= ruleAction ) )
            	    {
            	    otherlv_1=(Token)match(input,Comma,FOLLOW_34); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_1, grammarAccess.getConsequentAccess().getCommaKeyword_1_0());
            	      			
            	    }
            	    // InternalProblemParser.g:2367:4: ( (lv_actions_2_0= ruleAction ) )
            	    // InternalProblemParser.g:2368:5: (lv_actions_2_0= ruleAction )
            	    {
            	    // InternalProblemParser.g:2368:5: (lv_actions_2_0= ruleAction )
            	    // InternalProblemParser.g:2369:6: lv_actions_2_0= ruleAction
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getConsequentAccess().getActionsActionParserRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_48);
            	    lv_actions_2_0=ruleAction();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getConsequentRule());
            	      						}
            	      						add(
            	      							current,
            	      							"actions",
            	      							lv_actions_2_0,
            	      							"tools.refinery.language.Problem.Action");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop57;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleConsequent"


    // $ANTLR start "entryRuleAction"
    // InternalProblemParser.g:2391:1: entryRuleAction returns [EObject current=null] : iv_ruleAction= ruleAction EOF ;
    public final EObject entryRuleAction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAction = null;


        try {
            // InternalProblemParser.g:2391:47: (iv_ruleAction= ruleAction EOF )
            // InternalProblemParser.g:2392:2: iv_ruleAction= ruleAction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getActionRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAction=ruleAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAction; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAction"


    // $ANTLR start "ruleAction"
    // InternalProblemParser.g:2398:1: ruleAction returns [EObject current=null] : (this_AssertionAction_0= ruleAssertionAction | this_TheoryAction_1= ruleTheoryAction ) ;
    public final EObject ruleAction() throws RecognitionException {
        EObject current = null;

        EObject this_AssertionAction_0 = null;

        EObject this_TheoryAction_1 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2404:2: ( (this_AssertionAction_0= ruleAssertionAction | this_TheoryAction_1= ruleTheoryAction ) )
            // InternalProblemParser.g:2405:2: (this_AssertionAction_0= ruleAssertionAction | this_TheoryAction_1= ruleTheoryAction )
            {
            // InternalProblemParser.g:2405:2: (this_AssertionAction_0= ruleAssertionAction | this_TheoryAction_1= ruleTheoryAction )
            int alt58=2;
            alt58 = dfa58.predict(input);
            switch (alt58) {
                case 1 :
                    // InternalProblemParser.g:2406:3: this_AssertionAction_0= ruleAssertionAction
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getActionAccess().getAssertionActionParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_AssertionAction_0=ruleAssertionAction();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_AssertionAction_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:2415:3: this_TheoryAction_1= ruleTheoryAction
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getActionAccess().getTheoryActionParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_TheoryAction_1=ruleTheoryAction();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_TheoryAction_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAction"


    // $ANTLR start "entryRuleAssertionAction"
    // InternalProblemParser.g:2427:1: entryRuleAssertionAction returns [EObject current=null] : iv_ruleAssertionAction= ruleAssertionAction EOF ;
    public final EObject entryRuleAssertionAction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAssertionAction = null;


        try {
            // InternalProblemParser.g:2427:56: (iv_ruleAssertionAction= ruleAssertionAction EOF )
            // InternalProblemParser.g:2428:2: iv_ruleAssertionAction= ruleAssertionAction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAssertionActionRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAssertionAction=ruleAssertionAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAssertionAction; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAssertionAction"


    // $ANTLR start "ruleAssertionAction"
    // InternalProblemParser.g:2434:1: ruleAssertionAction returns [EObject current=null] : ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) ) | ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis ) ) ;
    public final EObject ruleAssertionAction() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        Token otherlv_6=null;
        Token otherlv_10=null;
        Token otherlv_12=null;
        Token otherlv_14=null;
        EObject lv_arguments_2_0 = null;

        EObject lv_arguments_4_0 = null;

        EObject lv_value_7_0 = null;

        EObject lv_value_8_0 = null;

        EObject lv_arguments_11_0 = null;

        EObject lv_arguments_13_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2440:2: ( ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) ) | ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis ) ) )
            // InternalProblemParser.g:2441:2: ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) ) | ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis ) )
            {
            // InternalProblemParser.g:2441:2: ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) ) | ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis ) )
            int alt63=2;
            alt63 = dfa63.predict(input);
            switch (alt63) {
                case 1 :
                    // InternalProblemParser.g:2442:3: ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) )
                    {
                    // InternalProblemParser.g:2442:3: ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) )
                    // InternalProblemParser.g:2443:4: ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) )
                    {
                    // InternalProblemParser.g:2443:4: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:2444:5: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:2444:5: ( ruleQualifiedName )
                    // InternalProblemParser.g:2445:6: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getAssertionActionRule());
                      						}
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAssertionActionAccess().getRelationRelationCrossReference_0_0_0());
                      					
                    }
                    pushFollow(FOLLOW_21);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    otherlv_1=(Token)match(input,LeftParenthesis,FOLLOW_51); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_1, grammarAccess.getAssertionActionAccess().getLeftParenthesisKeyword_0_1());
                      			
                    }
                    // InternalProblemParser.g:2463:4: ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )?
                    int alt60=2;
                    int LA60_0 = input.LA(1);

                    if ( ((LA60_0>=Concretization && LA60_0<=Aggregator)||(LA60_0>=Container && LA60_0<=Primitive)||(LA60_0>=Contains && LA60_0<=Opposite)||(LA60_0>=Problem && LA60_0<=Subsets)||LA60_0==Assert||LA60_0==Module||LA60_0==Shadow||LA60_0==Multi||LA60_0==Atom||LA60_0==ColonColon||LA60_0==As||LA60_0==Asterisk||LA60_0==RULE_ID||LA60_0==RULE_QUOTED_ID) ) {
                        alt60=1;
                    }
                    switch (alt60) {
                        case 1 :
                            // InternalProblemParser.g:2464:5: ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )*
                            {
                            // InternalProblemParser.g:2464:5: ( (lv_arguments_2_0= ruleAssertionArgument ) )
                            // InternalProblemParser.g:2465:6: (lv_arguments_2_0= ruleAssertionArgument )
                            {
                            // InternalProblemParser.g:2465:6: (lv_arguments_2_0= ruleAssertionArgument )
                            // InternalProblemParser.g:2466:7: lv_arguments_2_0= ruleAssertionArgument
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getAssertionActionAccess().getArgumentsAssertionArgumentParserRuleCall_0_2_0_0());
                              						
                            }
                            pushFollow(FOLLOW_23);
                            lv_arguments_2_0=ruleAssertionArgument();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                              							}
                              							add(
                              								current,
                              								"arguments",
                              								lv_arguments_2_0,
                              								"tools.refinery.language.Problem.AssertionArgument");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }

                            // InternalProblemParser.g:2483:5: (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )*
                            loop59:
                            do {
                                int alt59=2;
                                int LA59_0 = input.LA(1);

                                if ( (LA59_0==Comma) ) {
                                    alt59=1;
                                }


                                switch (alt59) {
                            	case 1 :
                            	    // InternalProblemParser.g:2484:6: otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) )
                            	    {
                            	    otherlv_3=(Token)match(input,Comma,FOLLOW_52); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      						newLeafNode(otherlv_3, grammarAccess.getAssertionActionAccess().getCommaKeyword_0_2_1_0());
                            	      					
                            	    }
                            	    // InternalProblemParser.g:2488:6: ( (lv_arguments_4_0= ruleAssertionArgument ) )
                            	    // InternalProblemParser.g:2489:7: (lv_arguments_4_0= ruleAssertionArgument )
                            	    {
                            	    // InternalProblemParser.g:2489:7: (lv_arguments_4_0= ruleAssertionArgument )
                            	    // InternalProblemParser.g:2490:8: lv_arguments_4_0= ruleAssertionArgument
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      								newCompositeNode(grammarAccess.getAssertionActionAccess().getArgumentsAssertionArgumentParserRuleCall_0_2_1_1_0());
                            	      							
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_arguments_4_0=ruleAssertionArgument();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      								if (current==null) {
                            	      									current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                            	      								}
                            	      								add(
                            	      									current,
                            	      									"arguments",
                            	      									lv_arguments_4_0,
                            	      									"tools.refinery.language.Problem.AssertionArgument");
                            	      								afterParserOrEnumRuleCall();
                            	      							
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop59;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_5=(Token)match(input,RightParenthesis,FOLLOW_53); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_5, grammarAccess.getAssertionActionAccess().getRightParenthesisKeyword_0_3());
                      			
                    }
                    otherlv_6=(Token)match(input,Colon,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_6, grammarAccess.getAssertionActionAccess().getColonKeyword_0_4());
                      			
                    }
                    // InternalProblemParser.g:2517:4: ( (lv_value_7_0= ruleExpr ) )
                    // InternalProblemParser.g:2518:5: (lv_value_7_0= ruleExpr )
                    {
                    // InternalProblemParser.g:2518:5: (lv_value_7_0= ruleExpr )
                    // InternalProblemParser.g:2519:6: lv_value_7_0= ruleExpr
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAssertionActionAccess().getValueExprParserRuleCall_0_5_0());
                      					
                    }
                    pushFollow(FOLLOW_2);
                    lv_value_7_0=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                      						}
                      						set(
                      							current,
                      							"value",
                      							lv_value_7_0,
                      							"tools.refinery.language.Problem.Expr");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:2538:3: ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis )
                    {
                    // InternalProblemParser.g:2538:3: ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis )
                    // InternalProblemParser.g:2539:4: ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis
                    {
                    // InternalProblemParser.g:2539:4: ( (lv_value_8_0= ruleShortLogicConstant ) )
                    // InternalProblemParser.g:2540:5: (lv_value_8_0= ruleShortLogicConstant )
                    {
                    // InternalProblemParser.g:2540:5: (lv_value_8_0= ruleShortLogicConstant )
                    // InternalProblemParser.g:2541:6: lv_value_8_0= ruleShortLogicConstant
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAssertionActionAccess().getValueShortLogicConstantParserRuleCall_1_0_0());
                      					
                    }
                    pushFollow(FOLLOW_8);
                    lv_value_8_0=ruleShortLogicConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                      						}
                      						set(
                      							current,
                      							"value",
                      							lv_value_8_0,
                      							"tools.refinery.language.Problem.ShortLogicConstant");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    // InternalProblemParser.g:2558:4: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:2559:5: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:2559:5: ( ruleQualifiedName )
                    // InternalProblemParser.g:2560:6: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getAssertionActionRule());
                      						}
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAssertionActionAccess().getRelationRelationCrossReference_1_1_0());
                      					
                    }
                    pushFollow(FOLLOW_21);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    otherlv_10=(Token)match(input,LeftParenthesis,FOLLOW_51); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_10, grammarAccess.getAssertionActionAccess().getLeftParenthesisKeyword_1_2());
                      			
                    }
                    // InternalProblemParser.g:2578:4: ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )?
                    int alt62=2;
                    int LA62_0 = input.LA(1);

                    if ( ((LA62_0>=Concretization && LA62_0<=Aggregator)||(LA62_0>=Container && LA62_0<=Primitive)||(LA62_0>=Contains && LA62_0<=Opposite)||(LA62_0>=Problem && LA62_0<=Subsets)||LA62_0==Assert||LA62_0==Module||LA62_0==Shadow||LA62_0==Multi||LA62_0==Atom||LA62_0==ColonColon||LA62_0==As||LA62_0==Asterisk||LA62_0==RULE_ID||LA62_0==RULE_QUOTED_ID) ) {
                        alt62=1;
                    }
                    switch (alt62) {
                        case 1 :
                            // InternalProblemParser.g:2579:5: ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )*
                            {
                            // InternalProblemParser.g:2579:5: ( (lv_arguments_11_0= ruleAssertionArgument ) )
                            // InternalProblemParser.g:2580:6: (lv_arguments_11_0= ruleAssertionArgument )
                            {
                            // InternalProblemParser.g:2580:6: (lv_arguments_11_0= ruleAssertionArgument )
                            // InternalProblemParser.g:2581:7: lv_arguments_11_0= ruleAssertionArgument
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getAssertionActionAccess().getArgumentsAssertionArgumentParserRuleCall_1_3_0_0());
                              						
                            }
                            pushFollow(FOLLOW_23);
                            lv_arguments_11_0=ruleAssertionArgument();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                              							}
                              							add(
                              								current,
                              								"arguments",
                              								lv_arguments_11_0,
                              								"tools.refinery.language.Problem.AssertionArgument");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }

                            // InternalProblemParser.g:2598:5: (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )*
                            loop61:
                            do {
                                int alt61=2;
                                int LA61_0 = input.LA(1);

                                if ( (LA61_0==Comma) ) {
                                    alt61=1;
                                }


                                switch (alt61) {
                            	case 1 :
                            	    // InternalProblemParser.g:2599:6: otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) )
                            	    {
                            	    otherlv_12=(Token)match(input,Comma,FOLLOW_52); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      						newLeafNode(otherlv_12, grammarAccess.getAssertionActionAccess().getCommaKeyword_1_3_1_0());
                            	      					
                            	    }
                            	    // InternalProblemParser.g:2603:6: ( (lv_arguments_13_0= ruleAssertionArgument ) )
                            	    // InternalProblemParser.g:2604:7: (lv_arguments_13_0= ruleAssertionArgument )
                            	    {
                            	    // InternalProblemParser.g:2604:7: (lv_arguments_13_0= ruleAssertionArgument )
                            	    // InternalProblemParser.g:2605:8: lv_arguments_13_0= ruleAssertionArgument
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      								newCompositeNode(grammarAccess.getAssertionActionAccess().getArgumentsAssertionArgumentParserRuleCall_1_3_1_1_0());
                            	      							
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_arguments_13_0=ruleAssertionArgument();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      								if (current==null) {
                            	      									current = createModelElementForParent(grammarAccess.getAssertionActionRule());
                            	      								}
                            	      								add(
                            	      									current,
                            	      									"arguments",
                            	      									lv_arguments_13_0,
                            	      									"tools.refinery.language.Problem.AssertionArgument");
                            	      								afterParserOrEnumRuleCall();
                            	      							
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop61;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_14=(Token)match(input,RightParenthesis,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_14, grammarAccess.getAssertionActionAccess().getRightParenthesisKeyword_1_4());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAssertionAction"


    // $ANTLR start "entryRuleTheoryAction"
    // InternalProblemParser.g:2633:1: entryRuleTheoryAction returns [EObject current=null] : iv_ruleTheoryAction= ruleTheoryAction EOF ;
    public final EObject entryRuleTheoryAction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTheoryAction = null;


        try {
            // InternalProblemParser.g:2633:53: (iv_ruleTheoryAction= ruleTheoryAction EOF )
            // InternalProblemParser.g:2634:2: iv_ruleTheoryAction= ruleTheoryAction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTheoryActionRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleTheoryAction=ruleTheoryAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTheoryAction; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleTheoryAction"


    // $ANTLR start "ruleTheoryAction"
    // InternalProblemParser.g:2640:1: ruleTheoryAction returns [EObject current=null] : (otherlv_0= Assert ( (lv_term_1_0= ruleExpr ) ) ) ;
    public final EObject ruleTheoryAction() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_term_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2646:2: ( (otherlv_0= Assert ( (lv_term_1_0= ruleExpr ) ) ) )
            // InternalProblemParser.g:2647:2: (otherlv_0= Assert ( (lv_term_1_0= ruleExpr ) ) )
            {
            // InternalProblemParser.g:2647:2: (otherlv_0= Assert ( (lv_term_1_0= ruleExpr ) ) )
            // InternalProblemParser.g:2648:3: otherlv_0= Assert ( (lv_term_1_0= ruleExpr ) )
            {
            otherlv_0=(Token)match(input,Assert,FOLLOW_28); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getTheoryActionAccess().getAssertKeyword_0());
              		
            }
            // InternalProblemParser.g:2652:3: ( (lv_term_1_0= ruleExpr ) )
            // InternalProblemParser.g:2653:4: (lv_term_1_0= ruleExpr )
            {
            // InternalProblemParser.g:2653:4: (lv_term_1_0= ruleExpr )
            // InternalProblemParser.g:2654:5: lv_term_1_0= ruleExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getTheoryActionAccess().getTermExprParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_term_1_0=ruleExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getTheoryActionRule());
              					}
              					set(
              						current,
              						"term",
              						lv_term_1_0,
              						"tools.refinery.language.Problem.Expr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleTheoryAction"


    // $ANTLR start "entryRuleExpr"
    // InternalProblemParser.g:2675:1: entryRuleExpr returns [EObject current=null] : iv_ruleExpr= ruleExpr EOF ;
    public final EObject entryRuleExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExpr = null;


        try {
            // InternalProblemParser.g:2675:45: (iv_ruleExpr= ruleExpr EOF )
            // InternalProblemParser.g:2676:2: iv_ruleExpr= ruleExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleExpr=ruleExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleExpr"


    // $ANTLR start "ruleExpr"
    // InternalProblemParser.g:2682:1: ruleExpr returns [EObject current=null] : this_AssignmentExpr_0= ruleAssignmentExpr ;
    public final EObject ruleExpr() throws RecognitionException {
        EObject current = null;

        EObject this_AssignmentExpr_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2688:2: (this_AssignmentExpr_0= ruleAssignmentExpr )
            // InternalProblemParser.g:2689:2: this_AssignmentExpr_0= ruleAssignmentExpr
            {
            if ( state.backtracking==0 ) {

              		newCompositeNode(grammarAccess.getExprAccess().getAssignmentExprParserRuleCall());
              	
            }
            pushFollow(FOLLOW_2);
            this_AssignmentExpr_0=ruleAssignmentExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current = this_AssignmentExpr_0;
              		afterParserOrEnumRuleCall();
              	
            }

            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleExpr"


    // $ANTLR start "entryRuleAssignmentExpr"
    // InternalProblemParser.g:2700:1: entryRuleAssignmentExpr returns [EObject current=null] : iv_ruleAssignmentExpr= ruleAssignmentExpr EOF ;
    public final EObject entryRuleAssignmentExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAssignmentExpr = null;


        try {
            // InternalProblemParser.g:2700:55: (iv_ruleAssignmentExpr= ruleAssignmentExpr EOF )
            // InternalProblemParser.g:2701:2: iv_ruleAssignmentExpr= ruleAssignmentExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAssignmentExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAssignmentExpr=ruleAssignmentExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAssignmentExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAssignmentExpr"


    // $ANTLR start "ruleAssignmentExpr"
    // InternalProblemParser.g:2707:1: ruleAssignmentExpr returns [EObject current=null] : (this_BooleanExpr_0= ruleBooleanExpr ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )* ) ;
    public final EObject ruleAssignmentExpr() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        EObject this_BooleanExpr_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2713:2: ( (this_BooleanExpr_0= ruleBooleanExpr ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )* ) )
            // InternalProblemParser.g:2714:2: (this_BooleanExpr_0= ruleBooleanExpr ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )* )
            {
            // InternalProblemParser.g:2714:2: (this_BooleanExpr_0= ruleBooleanExpr ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )* )
            // InternalProblemParser.g:2715:3: this_BooleanExpr_0= ruleBooleanExpr ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getAssignmentExprAccess().getBooleanExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_54);
            this_BooleanExpr_0=ruleBooleanExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_BooleanExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:2723:3: ( () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) ) )*
            loop64:
            do {
                int alt64=2;
                int LA64_0 = input.LA(1);

                if ( (LA64_0==Is) ) {
                    alt64=1;
                }


                switch (alt64) {
            	case 1 :
            	    // InternalProblemParser.g:2724:4: () otherlv_2= Is ( (lv_right_3_0= ruleBooleanExpr ) )
            	    {
            	    // InternalProblemParser.g:2724:4: ()
            	    // InternalProblemParser.g:2725:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getAssignmentExprAccess().getAssignmentExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    otherlv_2=(Token)match(input,Is,FOLLOW_28); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_2, grammarAccess.getAssignmentExprAccess().getIsKeyword_1_1());
            	      			
            	    }
            	    // InternalProblemParser.g:2735:4: ( (lv_right_3_0= ruleBooleanExpr ) )
            	    // InternalProblemParser.g:2736:5: (lv_right_3_0= ruleBooleanExpr )
            	    {
            	    // InternalProblemParser.g:2736:5: (lv_right_3_0= ruleBooleanExpr )
            	    // InternalProblemParser.g:2737:6: lv_right_3_0= ruleBooleanExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getAssignmentExprAccess().getRightBooleanExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_54);
            	    lv_right_3_0=ruleBooleanExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getAssignmentExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.BooleanExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop64;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAssignmentExpr"


    // $ANTLR start "entryRuleBooleanExpr"
    // InternalProblemParser.g:2759:1: entryRuleBooleanExpr returns [EObject current=null] : iv_ruleBooleanExpr= ruleBooleanExpr EOF ;
    public final EObject entryRuleBooleanExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleBooleanExpr = null;


        try {
            // InternalProblemParser.g:2759:52: (iv_ruleBooleanExpr= ruleBooleanExpr EOF )
            // InternalProblemParser.g:2760:2: iv_ruleBooleanExpr= ruleBooleanExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getBooleanExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleBooleanExpr=ruleBooleanExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleBooleanExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleBooleanExpr"


    // $ANTLR start "ruleBooleanExpr"
    // InternalProblemParser.g:2766:1: ruleBooleanExpr returns [EObject current=null] : (this_ComparisonExpr_0= ruleComparisonExpr ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )* ) ;
    public final EObject ruleBooleanExpr() throws RecognitionException {
        EObject current = null;

        EObject this_ComparisonExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2772:2: ( (this_ComparisonExpr_0= ruleComparisonExpr ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )* ) )
            // InternalProblemParser.g:2773:2: (this_ComparisonExpr_0= ruleComparisonExpr ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )* )
            {
            // InternalProblemParser.g:2773:2: (this_ComparisonExpr_0= ruleComparisonExpr ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )* )
            // InternalProblemParser.g:2774:3: this_ComparisonExpr_0= ruleComparisonExpr ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getBooleanExprAccess().getComparisonExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_55);
            this_ComparisonExpr_0=ruleComparisonExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_ComparisonExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:2782:3: ( () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) ) )*
            loop65:
            do {
                int alt65=2;
                int LA65_0 = input.LA(1);

                if ( (LA65_0==AmpersandAmpersand||LA65_0==CircumflexAccentCircumflexAccent||LA65_0==VerticalLineVerticalLine) ) {
                    alt65=1;
                }


                switch (alt65) {
            	case 1 :
            	    // InternalProblemParser.g:2783:4: () ( (lv_op_2_0= ruleBooleanBinaryOp ) ) ( (lv_right_3_0= ruleComparisonExpr ) )
            	    {
            	    // InternalProblemParser.g:2783:4: ()
            	    // InternalProblemParser.g:2784:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getBooleanExprAccess().getArithmeticBinaryExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    // InternalProblemParser.g:2790:4: ( (lv_op_2_0= ruleBooleanBinaryOp ) )
            	    // InternalProblemParser.g:2791:5: (lv_op_2_0= ruleBooleanBinaryOp )
            	    {
            	    // InternalProblemParser.g:2791:5: (lv_op_2_0= ruleBooleanBinaryOp )
            	    // InternalProblemParser.g:2792:6: lv_op_2_0= ruleBooleanBinaryOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getBooleanExprAccess().getOpBooleanBinaryOpEnumRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_2_0=ruleBooleanBinaryOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getBooleanExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"op",
            	      							lv_op_2_0,
            	      							"tools.refinery.language.Problem.BooleanBinaryOp");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:2809:4: ( (lv_right_3_0= ruleComparisonExpr ) )
            	    // InternalProblemParser.g:2810:5: (lv_right_3_0= ruleComparisonExpr )
            	    {
            	    // InternalProblemParser.g:2810:5: (lv_right_3_0= ruleComparisonExpr )
            	    // InternalProblemParser.g:2811:6: lv_right_3_0= ruleComparisonExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getBooleanExprAccess().getRightComparisonExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_55);
            	    lv_right_3_0=ruleComparisonExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getBooleanExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.ComparisonExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop65;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleBooleanExpr"


    // $ANTLR start "entryRuleComparisonExpr"
    // InternalProblemParser.g:2833:1: entryRuleComparisonExpr returns [EObject current=null] : iv_ruleComparisonExpr= ruleComparisonExpr EOF ;
    public final EObject entryRuleComparisonExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleComparisonExpr = null;


        try {
            // InternalProblemParser.g:2833:55: (iv_ruleComparisonExpr= ruleComparisonExpr EOF )
            // InternalProblemParser.g:2834:2: iv_ruleComparisonExpr= ruleComparisonExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getComparisonExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleComparisonExpr=ruleComparisonExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleComparisonExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleComparisonExpr"


    // $ANTLR start "ruleComparisonExpr"
    // InternalProblemParser.g:2840:1: ruleComparisonExpr returns [EObject current=null] : (this_LatticeExpr_0= ruleLatticeExpr ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )* ) ;
    public final EObject ruleComparisonExpr() throws RecognitionException {
        EObject current = null;

        EObject this_LatticeExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;

        Enumerator lv_op_5_0 = null;

        EObject lv_right_6_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2846:2: ( (this_LatticeExpr_0= ruleLatticeExpr ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )* ) )
            // InternalProblemParser.g:2847:2: (this_LatticeExpr_0= ruleLatticeExpr ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )* )
            {
            // InternalProblemParser.g:2847:2: (this_LatticeExpr_0= ruleLatticeExpr ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )* )
            // InternalProblemParser.g:2848:3: this_LatticeExpr_0= ruleLatticeExpr ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getComparisonExprAccess().getLatticeExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_56);
            this_LatticeExpr_0=ruleLatticeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_LatticeExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:2856:3: ( ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) ) | ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) ) )*
            loop66:
            do {
                int alt66=3;
                int LA66_0 = input.LA(1);

                if ( (LA66_0==ExclamationMarkEqualsSign||(LA66_0>=LessThanSignEqualsSign && LA66_0<=GreaterThanSignEqualsSign)||LA66_0==LessThanSign||LA66_0==GreaterThanSign) ) {
                    alt66=1;
                }
                else if ( (LA66_0==ExclamationMarkEqualsSignEqualsSign||LA66_0==EqualsSignEqualsSignEqualsSign||(LA66_0>=ColonGreaterThanSign && LA66_0<=LessThanSignColon)) ) {
                    alt66=2;
                }


                switch (alt66) {
            	case 1 :
            	    // InternalProblemParser.g:2857:4: ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) )
            	    {
            	    // InternalProblemParser.g:2857:4: ( () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) ) )
            	    // InternalProblemParser.g:2858:5: () ( (lv_op_2_0= ruleComparisonOp ) ) ( (lv_right_3_0= ruleLatticeExpr ) )
            	    {
            	    // InternalProblemParser.g:2858:5: ()
            	    // InternalProblemParser.g:2859:6: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      						current = forceCreateModelElementAndSet(
            	      							grammarAccess.getComparisonExprAccess().getComparisonExprLeftAction_1_0_0(),
            	      							current);
            	      					
            	    }

            	    }

            	    // InternalProblemParser.g:2865:5: ( (lv_op_2_0= ruleComparisonOp ) )
            	    // InternalProblemParser.g:2866:6: (lv_op_2_0= ruleComparisonOp )
            	    {
            	    // InternalProblemParser.g:2866:6: (lv_op_2_0= ruleComparisonOp )
            	    // InternalProblemParser.g:2867:7: lv_op_2_0= ruleComparisonOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      							newCompositeNode(grammarAccess.getComparisonExprAccess().getOpComparisonOpEnumRuleCall_1_0_1_0());
            	      						
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_2_0=ruleComparisonOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      							if (current==null) {
            	      								current = createModelElementForParent(grammarAccess.getComparisonExprRule());
            	      							}
            	      							set(
            	      								current,
            	      								"op",
            	      								lv_op_2_0,
            	      								"tools.refinery.language.Problem.ComparisonOp");
            	      							afterParserOrEnumRuleCall();
            	      						
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:2884:5: ( (lv_right_3_0= ruleLatticeExpr ) )
            	    // InternalProblemParser.g:2885:6: (lv_right_3_0= ruleLatticeExpr )
            	    {
            	    // InternalProblemParser.g:2885:6: (lv_right_3_0= ruleLatticeExpr )
            	    // InternalProblemParser.g:2886:7: lv_right_3_0= ruleLatticeExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      							newCompositeNode(grammarAccess.getComparisonExprAccess().getRightLatticeExprParserRuleCall_1_0_2_0());
            	      						
            	    }
            	    pushFollow(FOLLOW_56);
            	    lv_right_3_0=ruleLatticeExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      							if (current==null) {
            	      								current = createModelElementForParent(grammarAccess.getComparisonExprRule());
            	      							}
            	      							set(
            	      								current,
            	      								"right",
            	      								lv_right_3_0,
            	      								"tools.refinery.language.Problem.LatticeExpr");
            	      							afterParserOrEnumRuleCall();
            	      						
            	    }

            	    }


            	    }


            	    }


            	    }
            	    break;
            	case 2 :
            	    // InternalProblemParser.g:2905:4: ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) )
            	    {
            	    // InternalProblemParser.g:2905:4: ( () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) ) )
            	    // InternalProblemParser.g:2906:5: () ( (lv_op_5_0= ruleLatticeComparisonOp ) ) ( (lv_right_6_0= ruleLatticeExpr ) )
            	    {
            	    // InternalProblemParser.g:2906:5: ()
            	    // InternalProblemParser.g:2907:6: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      						current = forceCreateModelElementAndSet(
            	      							grammarAccess.getComparisonExprAccess().getLatticeBinaryExprLeftAction_1_1_0(),
            	      							current);
            	      					
            	    }

            	    }

            	    // InternalProblemParser.g:2913:5: ( (lv_op_5_0= ruleLatticeComparisonOp ) )
            	    // InternalProblemParser.g:2914:6: (lv_op_5_0= ruleLatticeComparisonOp )
            	    {
            	    // InternalProblemParser.g:2914:6: (lv_op_5_0= ruleLatticeComparisonOp )
            	    // InternalProblemParser.g:2915:7: lv_op_5_0= ruleLatticeComparisonOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      							newCompositeNode(grammarAccess.getComparisonExprAccess().getOpLatticeComparisonOpEnumRuleCall_1_1_1_0());
            	      						
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_5_0=ruleLatticeComparisonOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      							if (current==null) {
            	      								current = createModelElementForParent(grammarAccess.getComparisonExprRule());
            	      							}
            	      							set(
            	      								current,
            	      								"op",
            	      								lv_op_5_0,
            	      								"tools.refinery.language.Problem.LatticeComparisonOp");
            	      							afterParserOrEnumRuleCall();
            	      						
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:2932:5: ( (lv_right_6_0= ruleLatticeExpr ) )
            	    // InternalProblemParser.g:2933:6: (lv_right_6_0= ruleLatticeExpr )
            	    {
            	    // InternalProblemParser.g:2933:6: (lv_right_6_0= ruleLatticeExpr )
            	    // InternalProblemParser.g:2934:7: lv_right_6_0= ruleLatticeExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      							newCompositeNode(grammarAccess.getComparisonExprAccess().getRightLatticeExprParserRuleCall_1_1_2_0());
            	      						
            	    }
            	    pushFollow(FOLLOW_56);
            	    lv_right_6_0=ruleLatticeExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      							if (current==null) {
            	      								current = createModelElementForParent(grammarAccess.getComparisonExprRule());
            	      							}
            	      							set(
            	      								current,
            	      								"right",
            	      								lv_right_6_0,
            	      								"tools.refinery.language.Problem.LatticeExpr");
            	      							afterParserOrEnumRuleCall();
            	      						
            	    }

            	    }


            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop66;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleComparisonExpr"


    // $ANTLR start "entryRuleLatticeExpr"
    // InternalProblemParser.g:2957:1: entryRuleLatticeExpr returns [EObject current=null] : iv_ruleLatticeExpr= ruleLatticeExpr EOF ;
    public final EObject entryRuleLatticeExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleLatticeExpr = null;


        try {
            // InternalProblemParser.g:2957:52: (iv_ruleLatticeExpr= ruleLatticeExpr EOF )
            // InternalProblemParser.g:2958:2: iv_ruleLatticeExpr= ruleLatticeExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getLatticeExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleLatticeExpr=ruleLatticeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleLatticeExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleLatticeExpr"


    // $ANTLR start "ruleLatticeExpr"
    // InternalProblemParser.g:2964:1: ruleLatticeExpr returns [EObject current=null] : (this_AdditiveExpr_0= ruleAdditiveExpr ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )* ) ;
    public final EObject ruleLatticeExpr() throws RecognitionException {
        EObject current = null;

        EObject this_AdditiveExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:2970:2: ( (this_AdditiveExpr_0= ruleAdditiveExpr ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )* ) )
            // InternalProblemParser.g:2971:2: (this_AdditiveExpr_0= ruleAdditiveExpr ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )* )
            {
            // InternalProblemParser.g:2971:2: (this_AdditiveExpr_0= ruleAdditiveExpr ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )* )
            // InternalProblemParser.g:2972:3: this_AdditiveExpr_0= ruleAdditiveExpr ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getLatticeExprAccess().getAdditiveExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_57);
            this_AdditiveExpr_0=ruleAdditiveExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_AdditiveExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:2980:3: ( () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) ) )*
            loop67:
            do {
                int alt67=2;
                int LA67_0 = input.LA(1);

                if ( (LA67_0==SolidusReverseSolidus||LA67_0==ReverseSolidusSolidus) ) {
                    alt67=1;
                }


                switch (alt67) {
            	case 1 :
            	    // InternalProblemParser.g:2981:4: () ( (lv_op_2_0= ruleLatticeBinaryOp ) ) ( (lv_right_3_0= ruleAdditiveExpr ) )
            	    {
            	    // InternalProblemParser.g:2981:4: ()
            	    // InternalProblemParser.g:2982:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getLatticeExprAccess().getLatticeBinaryExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    // InternalProblemParser.g:2988:4: ( (lv_op_2_0= ruleLatticeBinaryOp ) )
            	    // InternalProblemParser.g:2989:5: (lv_op_2_0= ruleLatticeBinaryOp )
            	    {
            	    // InternalProblemParser.g:2989:5: (lv_op_2_0= ruleLatticeBinaryOp )
            	    // InternalProblemParser.g:2990:6: lv_op_2_0= ruleLatticeBinaryOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getLatticeExprAccess().getOpLatticeBinaryOpEnumRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_2_0=ruleLatticeBinaryOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getLatticeExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"op",
            	      							lv_op_2_0,
            	      							"tools.refinery.language.Problem.LatticeBinaryOp");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:3007:4: ( (lv_right_3_0= ruleAdditiveExpr ) )
            	    // InternalProblemParser.g:3008:5: (lv_right_3_0= ruleAdditiveExpr )
            	    {
            	    // InternalProblemParser.g:3008:5: (lv_right_3_0= ruleAdditiveExpr )
            	    // InternalProblemParser.g:3009:6: lv_right_3_0= ruleAdditiveExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getLatticeExprAccess().getRightAdditiveExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_57);
            	    lv_right_3_0=ruleAdditiveExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getLatticeExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.AdditiveExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop67;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleLatticeExpr"


    // $ANTLR start "entryRuleAdditiveExpr"
    // InternalProblemParser.g:3031:1: entryRuleAdditiveExpr returns [EObject current=null] : iv_ruleAdditiveExpr= ruleAdditiveExpr EOF ;
    public final EObject entryRuleAdditiveExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAdditiveExpr = null;


        try {
            // InternalProblemParser.g:3031:53: (iv_ruleAdditiveExpr= ruleAdditiveExpr EOF )
            // InternalProblemParser.g:3032:2: iv_ruleAdditiveExpr= ruleAdditiveExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAdditiveExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAdditiveExpr=ruleAdditiveExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAdditiveExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAdditiveExpr"


    // $ANTLR start "ruleAdditiveExpr"
    // InternalProblemParser.g:3038:1: ruleAdditiveExpr returns [EObject current=null] : (this_MultiplicativeExpr_0= ruleMultiplicativeExpr ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )* ) ;
    public final EObject ruleAdditiveExpr() throws RecognitionException {
        EObject current = null;

        EObject this_MultiplicativeExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3044:2: ( (this_MultiplicativeExpr_0= ruleMultiplicativeExpr ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )* ) )
            // InternalProblemParser.g:3045:2: (this_MultiplicativeExpr_0= ruleMultiplicativeExpr ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )* )
            {
            // InternalProblemParser.g:3045:2: (this_MultiplicativeExpr_0= ruleMultiplicativeExpr ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )* )
            // InternalProblemParser.g:3046:3: this_MultiplicativeExpr_0= ruleMultiplicativeExpr ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getAdditiveExprAccess().getMultiplicativeExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_58);
            this_MultiplicativeExpr_0=ruleMultiplicativeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_MultiplicativeExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:3054:3: ( () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) ) )*
            loop68:
            do {
                int alt68=2;
                int LA68_0 = input.LA(1);

                if ( (LA68_0==PlusSign||LA68_0==HyphenMinus) ) {
                    alt68=1;
                }


                switch (alt68) {
            	case 1 :
            	    // InternalProblemParser.g:3055:4: () ( (lv_op_2_0= ruleAdditiveOp ) ) ( (lv_right_3_0= ruleMultiplicativeExpr ) )
            	    {
            	    // InternalProblemParser.g:3055:4: ()
            	    // InternalProblemParser.g:3056:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getAdditiveExprAccess().getArithmeticBinaryExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    // InternalProblemParser.g:3062:4: ( (lv_op_2_0= ruleAdditiveOp ) )
            	    // InternalProblemParser.g:3063:5: (lv_op_2_0= ruleAdditiveOp )
            	    {
            	    // InternalProblemParser.g:3063:5: (lv_op_2_0= ruleAdditiveOp )
            	    // InternalProblemParser.g:3064:6: lv_op_2_0= ruleAdditiveOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getAdditiveExprAccess().getOpAdditiveOpEnumRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_2_0=ruleAdditiveOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getAdditiveExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"op",
            	      							lv_op_2_0,
            	      							"tools.refinery.language.Problem.AdditiveOp");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:3081:4: ( (lv_right_3_0= ruleMultiplicativeExpr ) )
            	    // InternalProblemParser.g:3082:5: (lv_right_3_0= ruleMultiplicativeExpr )
            	    {
            	    // InternalProblemParser.g:3082:5: (lv_right_3_0= ruleMultiplicativeExpr )
            	    // InternalProblemParser.g:3083:6: lv_right_3_0= ruleMultiplicativeExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getAdditiveExprAccess().getRightMultiplicativeExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_58);
            	    lv_right_3_0=ruleMultiplicativeExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getAdditiveExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.MultiplicativeExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop68;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAdditiveExpr"


    // $ANTLR start "entryRuleMultiplicativeExpr"
    // InternalProblemParser.g:3105:1: entryRuleMultiplicativeExpr returns [EObject current=null] : iv_ruleMultiplicativeExpr= ruleMultiplicativeExpr EOF ;
    public final EObject entryRuleMultiplicativeExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMultiplicativeExpr = null;


        try {
            // InternalProblemParser.g:3105:59: (iv_ruleMultiplicativeExpr= ruleMultiplicativeExpr EOF )
            // InternalProblemParser.g:3106:2: iv_ruleMultiplicativeExpr= ruleMultiplicativeExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMultiplicativeExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleMultiplicativeExpr=ruleMultiplicativeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMultiplicativeExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleMultiplicativeExpr"


    // $ANTLR start "ruleMultiplicativeExpr"
    // InternalProblemParser.g:3112:1: ruleMultiplicativeExpr returns [EObject current=null] : (this_ExponentialExpr_0= ruleExponentialExpr ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )* ) ;
    public final EObject ruleMultiplicativeExpr() throws RecognitionException {
        EObject current = null;

        EObject this_ExponentialExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3118:2: ( (this_ExponentialExpr_0= ruleExponentialExpr ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )* ) )
            // InternalProblemParser.g:3119:2: (this_ExponentialExpr_0= ruleExponentialExpr ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )* )
            {
            // InternalProblemParser.g:3119:2: (this_ExponentialExpr_0= ruleExponentialExpr ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )* )
            // InternalProblemParser.g:3120:3: this_ExponentialExpr_0= ruleExponentialExpr ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getMultiplicativeExprAccess().getExponentialExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_59);
            this_ExponentialExpr_0=ruleExponentialExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_ExponentialExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:3128:3: ( () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )*
            loop69:
            do {
                int alt69=2;
                int LA69_0 = input.LA(1);

                if ( (LA69_0==Asterisk||LA69_0==Solidus) ) {
                    alt69=1;
                }


                switch (alt69) {
            	case 1 :
            	    // InternalProblemParser.g:3129:4: () ( (lv_op_2_0= ruleMultiplicativeOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) )
            	    {
            	    // InternalProblemParser.g:3129:4: ()
            	    // InternalProblemParser.g:3130:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getMultiplicativeExprAccess().getArithmeticBinaryExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    // InternalProblemParser.g:3136:4: ( (lv_op_2_0= ruleMultiplicativeOp ) )
            	    // InternalProblemParser.g:3137:5: (lv_op_2_0= ruleMultiplicativeOp )
            	    {
            	    // InternalProblemParser.g:3137:5: (lv_op_2_0= ruleMultiplicativeOp )
            	    // InternalProblemParser.g:3138:6: lv_op_2_0= ruleMultiplicativeOp
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getMultiplicativeExprAccess().getOpMultiplicativeOpEnumRuleCall_1_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_28);
            	    lv_op_2_0=ruleMultiplicativeOp();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getMultiplicativeExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"op",
            	      							lv_op_2_0,
            	      							"tools.refinery.language.Problem.MultiplicativeOp");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }

            	    // InternalProblemParser.g:3155:4: ( (lv_right_3_0= ruleExponentialExpr ) )
            	    // InternalProblemParser.g:3156:5: (lv_right_3_0= ruleExponentialExpr )
            	    {
            	    // InternalProblemParser.g:3156:5: (lv_right_3_0= ruleExponentialExpr )
            	    // InternalProblemParser.g:3157:6: lv_right_3_0= ruleExponentialExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getMultiplicativeExprAccess().getRightExponentialExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_59);
            	    lv_right_3_0=ruleExponentialExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getMultiplicativeExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.ExponentialExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop69;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleMultiplicativeExpr"


    // $ANTLR start "entryRuleExponentialExpr"
    // InternalProblemParser.g:3179:1: entryRuleExponentialExpr returns [EObject current=null] : iv_ruleExponentialExpr= ruleExponentialExpr EOF ;
    public final EObject entryRuleExponentialExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExponentialExpr = null;


        try {
            // InternalProblemParser.g:3179:56: (iv_ruleExponentialExpr= ruleExponentialExpr EOF )
            // InternalProblemParser.g:3180:2: iv_ruleExponentialExpr= ruleExponentialExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getExponentialExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleExponentialExpr=ruleExponentialExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleExponentialExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleExponentialExpr"


    // $ANTLR start "ruleExponentialExpr"
    // InternalProblemParser.g:3186:1: ruleExponentialExpr returns [EObject current=null] : (this_RangeExpr_0= ruleRangeExpr ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )? ) ;
    public final EObject ruleExponentialExpr() throws RecognitionException {
        EObject current = null;

        EObject this_RangeExpr_0 = null;

        Enumerator lv_op_2_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3192:2: ( (this_RangeExpr_0= ruleRangeExpr ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )? ) )
            // InternalProblemParser.g:3193:2: (this_RangeExpr_0= ruleRangeExpr ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )? )
            {
            // InternalProblemParser.g:3193:2: (this_RangeExpr_0= ruleRangeExpr ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )? )
            // InternalProblemParser.g:3194:3: this_RangeExpr_0= ruleRangeExpr ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )?
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getExponentialExprAccess().getRangeExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_60);
            this_RangeExpr_0=ruleRangeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_RangeExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:3202:3: ( () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) ) )?
            int alt70=2;
            int LA70_0 = input.LA(1);

            if ( (LA70_0==AsteriskAsterisk) ) {
                alt70=1;
            }
            switch (alt70) {
                case 1 :
                    // InternalProblemParser.g:3203:4: () ( (lv_op_2_0= ruleExponentialOp ) ) ( (lv_right_3_0= ruleExponentialExpr ) )
                    {
                    // InternalProblemParser.g:3203:4: ()
                    // InternalProblemParser.g:3204:5: 
                    {
                    if ( state.backtracking==0 ) {

                      					current = forceCreateModelElementAndSet(
                      						grammarAccess.getExponentialExprAccess().getArithmeticBinaryExprLeftAction_1_0(),
                      						current);
                      				
                    }

                    }

                    // InternalProblemParser.g:3210:4: ( (lv_op_2_0= ruleExponentialOp ) )
                    // InternalProblemParser.g:3211:5: (lv_op_2_0= ruleExponentialOp )
                    {
                    // InternalProblemParser.g:3211:5: (lv_op_2_0= ruleExponentialOp )
                    // InternalProblemParser.g:3212:6: lv_op_2_0= ruleExponentialOp
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getExponentialExprAccess().getOpExponentialOpEnumRuleCall_1_1_0());
                      					
                    }
                    pushFollow(FOLLOW_28);
                    lv_op_2_0=ruleExponentialOp();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getExponentialExprRule());
                      						}
                      						set(
                      							current,
                      							"op",
                      							lv_op_2_0,
                      							"tools.refinery.language.Problem.ExponentialOp");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    // InternalProblemParser.g:3229:4: ( (lv_right_3_0= ruleExponentialExpr ) )
                    // InternalProblemParser.g:3230:5: (lv_right_3_0= ruleExponentialExpr )
                    {
                    // InternalProblemParser.g:3230:5: (lv_right_3_0= ruleExponentialExpr )
                    // InternalProblemParser.g:3231:6: lv_right_3_0= ruleExponentialExpr
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getExponentialExprAccess().getRightExponentialExprParserRuleCall_1_2_0());
                      					
                    }
                    pushFollow(FOLLOW_2);
                    lv_right_3_0=ruleExponentialExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getExponentialExprRule());
                      						}
                      						set(
                      							current,
                      							"right",
                      							lv_right_3_0,
                      							"tools.refinery.language.Problem.ExponentialExpr");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleExponentialExpr"


    // $ANTLR start "entryRuleRangeExpr"
    // InternalProblemParser.g:3253:1: entryRuleRangeExpr returns [EObject current=null] : iv_ruleRangeExpr= ruleRangeExpr EOF ;
    public final EObject entryRuleRangeExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRangeExpr = null;


        try {
            // InternalProblemParser.g:3253:50: (iv_ruleRangeExpr= ruleRangeExpr EOF )
            // InternalProblemParser.g:3254:2: iv_ruleRangeExpr= ruleRangeExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getRangeExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleRangeExpr=ruleRangeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleRangeExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleRangeExpr"


    // $ANTLR start "ruleRangeExpr"
    // InternalProblemParser.g:3260:1: ruleRangeExpr returns [EObject current=null] : (this_UnaryExpr_0= ruleUnaryExpr ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )* ) ;
    public final EObject ruleRangeExpr() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        EObject this_UnaryExpr_0 = null;

        EObject lv_right_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3266:2: ( (this_UnaryExpr_0= ruleUnaryExpr ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )* ) )
            // InternalProblemParser.g:3267:2: (this_UnaryExpr_0= ruleUnaryExpr ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )* )
            {
            // InternalProblemParser.g:3267:2: (this_UnaryExpr_0= ruleUnaryExpr ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )* )
            // InternalProblemParser.g:3268:3: this_UnaryExpr_0= ruleUnaryExpr ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )*
            {
            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getRangeExprAccess().getUnaryExprParserRuleCall_0());
              		
            }
            pushFollow(FOLLOW_61);
            this_UnaryExpr_0=ruleUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = this_UnaryExpr_0;
              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:3276:3: ( () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) ) )*
            loop71:
            do {
                int alt71=2;
                int LA71_0 = input.LA(1);

                if ( (LA71_0==FullStopFullStop) ) {
                    alt71=1;
                }


                switch (alt71) {
            	case 1 :
            	    // InternalProblemParser.g:3277:4: () otherlv_2= FullStopFullStop ( (lv_right_3_0= ruleUnaryExpr ) )
            	    {
            	    // InternalProblemParser.g:3277:4: ()
            	    // InternalProblemParser.g:3278:5: 
            	    {
            	    if ( state.backtracking==0 ) {

            	      					current = forceCreateModelElementAndSet(
            	      						grammarAccess.getRangeExprAccess().getRangeExprLeftAction_1_0(),
            	      						current);
            	      				
            	    }

            	    }

            	    otherlv_2=(Token)match(input,FullStopFullStop,FOLLOW_28); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_2, grammarAccess.getRangeExprAccess().getFullStopFullStopKeyword_1_1());
            	      			
            	    }
            	    // InternalProblemParser.g:3288:4: ( (lv_right_3_0= ruleUnaryExpr ) )
            	    // InternalProblemParser.g:3289:5: (lv_right_3_0= ruleUnaryExpr )
            	    {
            	    // InternalProblemParser.g:3289:5: (lv_right_3_0= ruleUnaryExpr )
            	    // InternalProblemParser.g:3290:6: lv_right_3_0= ruleUnaryExpr
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getRangeExprAccess().getRightUnaryExprParserRuleCall_1_2_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_61);
            	    lv_right_3_0=ruleUnaryExpr();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getRangeExprRule());
            	      						}
            	      						set(
            	      							current,
            	      							"right",
            	      							lv_right_3_0,
            	      							"tools.refinery.language.Problem.UnaryExpr");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop71;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleRangeExpr"


    // $ANTLR start "entryRuleUnaryExpr"
    // InternalProblemParser.g:3312:1: entryRuleUnaryExpr returns [EObject current=null] : iv_ruleUnaryExpr= ruleUnaryExpr EOF ;
    public final EObject entryRuleUnaryExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleUnaryExpr = null;


        try {
            // InternalProblemParser.g:3312:50: (iv_ruleUnaryExpr= ruleUnaryExpr EOF )
            // InternalProblemParser.g:3313:2: iv_ruleUnaryExpr= ruleUnaryExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getUnaryExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleUnaryExpr=ruleUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleUnaryExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleUnaryExpr"


    // $ANTLR start "ruleUnaryExpr"
    // InternalProblemParser.g:3319:1: ruleUnaryExpr returns [EObject current=null] : (this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr | this_NegationExpr_1= ruleNegationExpr | this_AggregationExpr_2= ruleAggregationExpr | this_ModalExpr_3= ruleModalExpr | this_Atom_4= ruleAtom | this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr | this_Constant_6= ruleConstant | (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis ) ) ;
    public final EObject ruleUnaryExpr() throws RecognitionException {
        EObject current = null;

        Token otherlv_7=null;
        Token otherlv_9=null;
        EObject this_ArithmeticUnaryExpr_0 = null;

        EObject this_NegationExpr_1 = null;

        EObject this_AggregationExpr_2 = null;

        EObject this_ModalExpr_3 = null;

        EObject this_Atom_4 = null;

        EObject this_VariableOrNodeExpr_5 = null;

        EObject this_Constant_6 = null;

        EObject this_Expr_8 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3325:2: ( (this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr | this_NegationExpr_1= ruleNegationExpr | this_AggregationExpr_2= ruleAggregationExpr | this_ModalExpr_3= ruleModalExpr | this_Atom_4= ruleAtom | this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr | this_Constant_6= ruleConstant | (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis ) ) )
            // InternalProblemParser.g:3326:2: (this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr | this_NegationExpr_1= ruleNegationExpr | this_AggregationExpr_2= ruleAggregationExpr | this_ModalExpr_3= ruleModalExpr | this_Atom_4= ruleAtom | this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr | this_Constant_6= ruleConstant | (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis ) )
            {
            // InternalProblemParser.g:3326:2: (this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr | this_NegationExpr_1= ruleNegationExpr | this_AggregationExpr_2= ruleAggregationExpr | this_ModalExpr_3= ruleModalExpr | this_Atom_4= ruleAtom | this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr | this_Constant_6= ruleConstant | (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis ) )
            int alt72=8;
            alt72 = dfa72.predict(input);
            switch (alt72) {
                case 1 :
                    // InternalProblemParser.g:3327:3: this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getArithmeticUnaryExprParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_ArithmeticUnaryExpr_0=ruleArithmeticUnaryExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_ArithmeticUnaryExpr_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:3336:3: this_NegationExpr_1= ruleNegationExpr
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getNegationExprParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_NegationExpr_1=ruleNegationExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_NegationExpr_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:3345:3: this_AggregationExpr_2= ruleAggregationExpr
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getAggregationExprParserRuleCall_2());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_AggregationExpr_2=ruleAggregationExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_AggregationExpr_2;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:3354:3: this_ModalExpr_3= ruleModalExpr
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getModalExprParserRuleCall_3());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_ModalExpr_3=ruleModalExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_ModalExpr_3;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:3363:3: this_Atom_4= ruleAtom
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getAtomParserRuleCall_4());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_Atom_4=ruleAtom();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_Atom_4;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 6 :
                    // InternalProblemParser.g:3372:3: this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getVariableOrNodeExprParserRuleCall_5());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_VariableOrNodeExpr_5=ruleVariableOrNodeExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_VariableOrNodeExpr_5;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 7 :
                    // InternalProblemParser.g:3381:3: this_Constant_6= ruleConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getUnaryExprAccess().getConstantParserRuleCall_6());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_Constant_6=ruleConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_Constant_6;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 8 :
                    // InternalProblemParser.g:3390:3: (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis )
                    {
                    // InternalProblemParser.g:3390:3: (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis )
                    // InternalProblemParser.g:3391:4: otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis
                    {
                    otherlv_7=(Token)match(input,LeftParenthesis,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_7, grammarAccess.getUnaryExprAccess().getLeftParenthesisKeyword_7_0());
                      			
                    }
                    if ( state.backtracking==0 ) {

                      				newCompositeNode(grammarAccess.getUnaryExprAccess().getExprParserRuleCall_7_1());
                      			
                    }
                    pushFollow(FOLLOW_62);
                    this_Expr_8=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = this_Expr_8;
                      				afterParserOrEnumRuleCall();
                      			
                    }
                    otherlv_9=(Token)match(input,RightParenthesis,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_9, grammarAccess.getUnaryExprAccess().getRightParenthesisKeyword_7_2());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleUnaryExpr"


    // $ANTLR start "entryRuleArithmeticUnaryExpr"
    // InternalProblemParser.g:3412:1: entryRuleArithmeticUnaryExpr returns [EObject current=null] : iv_ruleArithmeticUnaryExpr= ruleArithmeticUnaryExpr EOF ;
    public final EObject entryRuleArithmeticUnaryExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleArithmeticUnaryExpr = null;


        try {
            // InternalProblemParser.g:3412:60: (iv_ruleArithmeticUnaryExpr= ruleArithmeticUnaryExpr EOF )
            // InternalProblemParser.g:3413:2: iv_ruleArithmeticUnaryExpr= ruleArithmeticUnaryExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getArithmeticUnaryExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleArithmeticUnaryExpr=ruleArithmeticUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleArithmeticUnaryExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleArithmeticUnaryExpr"


    // $ANTLR start "ruleArithmeticUnaryExpr"
    // InternalProblemParser.g:3419:1: ruleArithmeticUnaryExpr returns [EObject current=null] : ( ( (lv_op_0_0= ruleUnaryOp ) ) ( (lv_body_1_0= ruleUnaryExpr ) ) ) ;
    public final EObject ruleArithmeticUnaryExpr() throws RecognitionException {
        EObject current = null;

        Enumerator lv_op_0_0 = null;

        EObject lv_body_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3425:2: ( ( ( (lv_op_0_0= ruleUnaryOp ) ) ( (lv_body_1_0= ruleUnaryExpr ) ) ) )
            // InternalProblemParser.g:3426:2: ( ( (lv_op_0_0= ruleUnaryOp ) ) ( (lv_body_1_0= ruleUnaryExpr ) ) )
            {
            // InternalProblemParser.g:3426:2: ( ( (lv_op_0_0= ruleUnaryOp ) ) ( (lv_body_1_0= ruleUnaryExpr ) ) )
            // InternalProblemParser.g:3427:3: ( (lv_op_0_0= ruleUnaryOp ) ) ( (lv_body_1_0= ruleUnaryExpr ) )
            {
            // InternalProblemParser.g:3427:3: ( (lv_op_0_0= ruleUnaryOp ) )
            // InternalProblemParser.g:3428:4: (lv_op_0_0= ruleUnaryOp )
            {
            // InternalProblemParser.g:3428:4: (lv_op_0_0= ruleUnaryOp )
            // InternalProblemParser.g:3429:5: lv_op_0_0= ruleUnaryOp
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getArithmeticUnaryExprAccess().getOpUnaryOpEnumRuleCall_0_0());
              				
            }
            pushFollow(FOLLOW_28);
            lv_op_0_0=ruleUnaryOp();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getArithmeticUnaryExprRule());
              					}
              					set(
              						current,
              						"op",
              						lv_op_0_0,
              						"tools.refinery.language.Problem.UnaryOp");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:3446:3: ( (lv_body_1_0= ruleUnaryExpr ) )
            // InternalProblemParser.g:3447:4: (lv_body_1_0= ruleUnaryExpr )
            {
            // InternalProblemParser.g:3447:4: (lv_body_1_0= ruleUnaryExpr )
            // InternalProblemParser.g:3448:5: lv_body_1_0= ruleUnaryExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getArithmeticUnaryExprAccess().getBodyUnaryExprParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_body_1_0=ruleUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getArithmeticUnaryExprRule());
              					}
              					set(
              						current,
              						"body",
              						lv_body_1_0,
              						"tools.refinery.language.Problem.UnaryExpr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleArithmeticUnaryExpr"


    // $ANTLR start "entryRuleNegationExpr"
    // InternalProblemParser.g:3469:1: entryRuleNegationExpr returns [EObject current=null] : iv_ruleNegationExpr= ruleNegationExpr EOF ;
    public final EObject entryRuleNegationExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNegationExpr = null;


        try {
            // InternalProblemParser.g:3469:53: (iv_ruleNegationExpr= ruleNegationExpr EOF )
            // InternalProblemParser.g:3470:2: iv_ruleNegationExpr= ruleNegationExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNegationExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleNegationExpr=ruleNegationExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNegationExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleNegationExpr"


    // $ANTLR start "ruleNegationExpr"
    // InternalProblemParser.g:3476:1: ruleNegationExpr returns [EObject current=null] : (otherlv_0= ExclamationMark ( (lv_body_1_0= ruleUnaryExpr ) ) ) ;
    public final EObject ruleNegationExpr() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_body_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3482:2: ( (otherlv_0= ExclamationMark ( (lv_body_1_0= ruleUnaryExpr ) ) ) )
            // InternalProblemParser.g:3483:2: (otherlv_0= ExclamationMark ( (lv_body_1_0= ruleUnaryExpr ) ) )
            {
            // InternalProblemParser.g:3483:2: (otherlv_0= ExclamationMark ( (lv_body_1_0= ruleUnaryExpr ) ) )
            // InternalProblemParser.g:3484:3: otherlv_0= ExclamationMark ( (lv_body_1_0= ruleUnaryExpr ) )
            {
            otherlv_0=(Token)match(input,ExclamationMark,FOLLOW_28); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getNegationExprAccess().getExclamationMarkKeyword_0());
              		
            }
            // InternalProblemParser.g:3488:3: ( (lv_body_1_0= ruleUnaryExpr ) )
            // InternalProblemParser.g:3489:4: (lv_body_1_0= ruleUnaryExpr )
            {
            // InternalProblemParser.g:3489:4: (lv_body_1_0= ruleUnaryExpr )
            // InternalProblemParser.g:3490:5: lv_body_1_0= ruleUnaryExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getNegationExprAccess().getBodyUnaryExprParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_body_1_0=ruleUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getNegationExprRule());
              					}
              					set(
              						current,
              						"body",
              						lv_body_1_0,
              						"tools.refinery.language.Problem.UnaryExpr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleNegationExpr"


    // $ANTLR start "entryRuleAggregationExpr"
    // InternalProblemParser.g:3511:1: entryRuleAggregationExpr returns [EObject current=null] : iv_ruleAggregationExpr= ruleAggregationExpr EOF ;
    public final EObject entryRuleAggregationExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAggregationExpr = null;


        try {
            // InternalProblemParser.g:3511:56: (iv_ruleAggregationExpr= ruleAggregationExpr EOF )
            // InternalProblemParser.g:3512:2: iv_ruleAggregationExpr= ruleAggregationExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAggregationExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAggregationExpr=ruleAggregationExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAggregationExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAggregationExpr"


    // $ANTLR start "ruleAggregationExpr"
    // InternalProblemParser.g:3518:1: ruleAggregationExpr returns [EObject current=null] : ( ( ( ruleQualifiedName ) ) otherlv_1= LeftCurlyBracket ( (lv_condition_2_0= ruleExpr ) ) (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )? otherlv_5= RightCurlyBracket ) ;
    public final EObject ruleAggregationExpr() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        EObject lv_condition_2_0 = null;

        EObject lv_value_4_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3524:2: ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftCurlyBracket ( (lv_condition_2_0= ruleExpr ) ) (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )? otherlv_5= RightCurlyBracket ) )
            // InternalProblemParser.g:3525:2: ( ( ( ruleQualifiedName ) ) otherlv_1= LeftCurlyBracket ( (lv_condition_2_0= ruleExpr ) ) (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )? otherlv_5= RightCurlyBracket )
            {
            // InternalProblemParser.g:3525:2: ( ( ( ruleQualifiedName ) ) otherlv_1= LeftCurlyBracket ( (lv_condition_2_0= ruleExpr ) ) (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )? otherlv_5= RightCurlyBracket )
            // InternalProblemParser.g:3526:3: ( ( ruleQualifiedName ) ) otherlv_1= LeftCurlyBracket ( (lv_condition_2_0= ruleExpr ) ) (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )? otherlv_5= RightCurlyBracket
            {
            // InternalProblemParser.g:3526:3: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:3527:4: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:3527:4: ( ruleQualifiedName )
            // InternalProblemParser.g:3528:5: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getAggregationExprRule());
              					}
              				
            }
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getAggregationExprAccess().getAggregatorAggregatorDeclarationCrossReference_0_0());
              				
            }
            pushFollow(FOLLOW_63);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            otherlv_1=(Token)match(input,LeftCurlyBracket,FOLLOW_28); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_1, grammarAccess.getAggregationExprAccess().getLeftCurlyBracketKeyword_1());
              		
            }
            // InternalProblemParser.g:3546:3: ( (lv_condition_2_0= ruleExpr ) )
            // InternalProblemParser.g:3547:4: (lv_condition_2_0= ruleExpr )
            {
            // InternalProblemParser.g:3547:4: (lv_condition_2_0= ruleExpr )
            // InternalProblemParser.g:3548:5: lv_condition_2_0= ruleExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getAggregationExprAccess().getConditionExprParserRuleCall_2_0());
              				
            }
            pushFollow(FOLLOW_64);
            lv_condition_2_0=ruleExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getAggregationExprRule());
              					}
              					set(
              						current,
              						"condition",
              						lv_condition_2_0,
              						"tools.refinery.language.Problem.Expr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:3565:3: (otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) ) )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==HyphenMinusGreaterThanSign) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // InternalProblemParser.g:3566:4: otherlv_3= HyphenMinusGreaterThanSign ( (lv_value_4_0= ruleExpr ) )
                    {
                    otherlv_3=(Token)match(input,HyphenMinusGreaterThanSign,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_3, grammarAccess.getAggregationExprAccess().getHyphenMinusGreaterThanSignKeyword_3_0());
                      			
                    }
                    // InternalProblemParser.g:3570:4: ( (lv_value_4_0= ruleExpr ) )
                    // InternalProblemParser.g:3571:5: (lv_value_4_0= ruleExpr )
                    {
                    // InternalProblemParser.g:3571:5: (lv_value_4_0= ruleExpr )
                    // InternalProblemParser.g:3572:6: lv_value_4_0= ruleExpr
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAggregationExprAccess().getValueExprParserRuleCall_3_1_0());
                      					
                    }
                    pushFollow(FOLLOW_17);
                    lv_value_4_0=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getAggregationExprRule());
                      						}
                      						set(
                      							current,
                      							"value",
                      							lv_value_4_0,
                      							"tools.refinery.language.Problem.Expr");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }


                    }
                    break;

            }

            otherlv_5=(Token)match(input,RightCurlyBracket,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_5, grammarAccess.getAggregationExprAccess().getRightCurlyBracketKeyword_4());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAggregationExpr"


    // $ANTLR start "entryRuleModalExpr"
    // InternalProblemParser.g:3598:1: entryRuleModalExpr returns [EObject current=null] : iv_ruleModalExpr= ruleModalExpr EOF ;
    public final EObject entryRuleModalExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleModalExpr = null;


        try {
            // InternalProblemParser.g:3598:50: (iv_ruleModalExpr= ruleModalExpr EOF )
            // InternalProblemParser.g:3599:2: iv_ruleModalExpr= ruleModalExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getModalExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleModalExpr=ruleModalExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleModalExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleModalExpr"


    // $ANTLR start "ruleModalExpr"
    // InternalProblemParser.g:3605:1: ruleModalExpr returns [EObject current=null] : ( ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) ) ( (lv_body_4_0= ruleUnaryExpr ) ) ) ;
    public final EObject ruleModalExpr() throws RecognitionException {
        EObject current = null;

        Enumerator lv_concreteness_0_0 = null;

        Enumerator lv_modality_1_0 = null;

        Enumerator lv_modality_2_0 = null;

        Enumerator lv_concreteness_3_0 = null;

        EObject lv_body_4_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3611:2: ( ( ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) ) ( (lv_body_4_0= ruleUnaryExpr ) ) ) )
            // InternalProblemParser.g:3612:2: ( ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) ) ( (lv_body_4_0= ruleUnaryExpr ) ) )
            {
            // InternalProblemParser.g:3612:2: ( ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) ) ( (lv_body_4_0= ruleUnaryExpr ) ) )
            // InternalProblemParser.g:3613:3: ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) ) ( (lv_body_4_0= ruleUnaryExpr ) )
            {
            // InternalProblemParser.g:3613:3: ( ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? ) | ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? ) )
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==Candidate||LA76_0==Partial) ) {
                alt76=1;
            }
            else if ( (LA76_0==Must||LA76_0==May) ) {
                alt76=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 76, 0, input);

                throw nvae;
            }
            switch (alt76) {
                case 1 :
                    // InternalProblemParser.g:3614:4: ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? )
                    {
                    // InternalProblemParser.g:3614:4: ( ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )? )
                    // InternalProblemParser.g:3615:5: ( (lv_concreteness_0_0= ruleConcreteness ) ) ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )?
                    {
                    // InternalProblemParser.g:3615:5: ( (lv_concreteness_0_0= ruleConcreteness ) )
                    // InternalProblemParser.g:3616:6: (lv_concreteness_0_0= ruleConcreteness )
                    {
                    // InternalProblemParser.g:3616:6: (lv_concreteness_0_0= ruleConcreteness )
                    // InternalProblemParser.g:3617:7: lv_concreteness_0_0= ruleConcreteness
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getModalExprAccess().getConcretenessConcretenessEnumRuleCall_0_0_0_0());
                      						
                    }
                    pushFollow(FOLLOW_28);
                    lv_concreteness_0_0=ruleConcreteness();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getModalExprRule());
                      							}
                      							set(
                      								current,
                      								"concreteness",
                      								lv_concreteness_0_0,
                      								"tools.refinery.language.Problem.Concreteness");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:3634:5: ( ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality ) )?
                    int alt74=2;
                    int LA74_0 = input.LA(1);

                    if ( (LA74_0==Must) ) {
                        int LA74_1 = input.LA(2);

                        if ( (synpred1_InternalProblemParser()) ) {
                            alt74=1;
                        }
                    }
                    else if ( (LA74_0==May) ) {
                        int LA74_2 = input.LA(2);

                        if ( (synpred1_InternalProblemParser()) ) {
                            alt74=1;
                        }
                    }
                    switch (alt74) {
                        case 1 :
                            // InternalProblemParser.g:3635:6: ( ( ruleModality ) )=> (lv_modality_1_0= ruleModality )
                            {
                            // InternalProblemParser.g:3639:6: (lv_modality_1_0= ruleModality )
                            // InternalProblemParser.g:3640:7: lv_modality_1_0= ruleModality
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getModalExprAccess().getModalityModalityEnumRuleCall_0_0_1_0());
                              						
                            }
                            pushFollow(FOLLOW_28);
                            lv_modality_1_0=ruleModality();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getModalExprRule());
                              							}
                              							set(
                              								current,
                              								"modality",
                              								lv_modality_1_0,
                              								"tools.refinery.language.Problem.Modality");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }
                            break;

                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:3659:4: ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? )
                    {
                    // InternalProblemParser.g:3659:4: ( ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )? )
                    // InternalProblemParser.g:3660:5: ( (lv_modality_2_0= ruleModality ) ) ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )?
                    {
                    // InternalProblemParser.g:3660:5: ( (lv_modality_2_0= ruleModality ) )
                    // InternalProblemParser.g:3661:6: (lv_modality_2_0= ruleModality )
                    {
                    // InternalProblemParser.g:3661:6: (lv_modality_2_0= ruleModality )
                    // InternalProblemParser.g:3662:7: lv_modality_2_0= ruleModality
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getModalExprAccess().getModalityModalityEnumRuleCall_0_1_0_0());
                      						
                    }
                    pushFollow(FOLLOW_28);
                    lv_modality_2_0=ruleModality();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getModalExprRule());
                      							}
                      							set(
                      								current,
                      								"modality",
                      								lv_modality_2_0,
                      								"tools.refinery.language.Problem.Modality");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:3679:5: ( ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness ) )?
                    int alt75=2;
                    int LA75_0 = input.LA(1);

                    if ( (LA75_0==Partial) ) {
                        int LA75_1 = input.LA(2);

                        if ( (synpred2_InternalProblemParser()) ) {
                            alt75=1;
                        }
                    }
                    else if ( (LA75_0==Candidate) ) {
                        int LA75_2 = input.LA(2);

                        if ( (synpred2_InternalProblemParser()) ) {
                            alt75=1;
                        }
                    }
                    switch (alt75) {
                        case 1 :
                            // InternalProblemParser.g:3680:6: ( ( ruleConcreteness ) )=> (lv_concreteness_3_0= ruleConcreteness )
                            {
                            // InternalProblemParser.g:3684:6: (lv_concreteness_3_0= ruleConcreteness )
                            // InternalProblemParser.g:3685:7: lv_concreteness_3_0= ruleConcreteness
                            {
                            if ( state.backtracking==0 ) {

                              							newCompositeNode(grammarAccess.getModalExprAccess().getConcretenessConcretenessEnumRuleCall_0_1_1_0());
                              						
                            }
                            pushFollow(FOLLOW_28);
                            lv_concreteness_3_0=ruleConcreteness();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              							if (current==null) {
                              								current = createModelElementForParent(grammarAccess.getModalExprRule());
                              							}
                              							set(
                              								current,
                              								"concreteness",
                              								lv_concreteness_3_0,
                              								"tools.refinery.language.Problem.Concreteness");
                              							afterParserOrEnumRuleCall();
                              						
                            }

                            }


                            }
                            break;

                    }


                    }


                    }
                    break;

            }

            // InternalProblemParser.g:3704:3: ( (lv_body_4_0= ruleUnaryExpr ) )
            // InternalProblemParser.g:3705:4: (lv_body_4_0= ruleUnaryExpr )
            {
            // InternalProblemParser.g:3705:4: (lv_body_4_0= ruleUnaryExpr )
            // InternalProblemParser.g:3706:5: lv_body_4_0= ruleUnaryExpr
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getModalExprAccess().getBodyUnaryExprParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_body_4_0=ruleUnaryExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getModalExprRule());
              					}
              					set(
              						current,
              						"body",
              						lv_body_4_0,
              						"tools.refinery.language.Problem.UnaryExpr");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleModalExpr"


    // $ANTLR start "entryRuleAtom"
    // InternalProblemParser.g:3727:1: entryRuleAtom returns [EObject current=null] : iv_ruleAtom= ruleAtom EOF ;
    public final EObject entryRuleAtom() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAtom = null;


        try {
            // InternalProblemParser.g:3727:45: (iv_ruleAtom= ruleAtom EOF )
            // InternalProblemParser.g:3728:2: iv_ruleAtom= ruleAtom EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAtomRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAtom=ruleAtom();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAtom; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAtom"


    // $ANTLR start "ruleAtom"
    // InternalProblemParser.g:3734:1: ruleAtom returns [EObject current=null] : ( ( ( ruleQualifiedName ) ) ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )? otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )? otherlv_6= RightParenthesis ) ;
    public final EObject ruleAtom() throws RecognitionException {
        EObject current = null;

        Token lv_transitiveClosure_1_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        EObject lv_arguments_3_0 = null;

        EObject lv_arguments_5_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3740:2: ( ( ( ( ruleQualifiedName ) ) ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )? otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )? otherlv_6= RightParenthesis ) )
            // InternalProblemParser.g:3741:2: ( ( ( ruleQualifiedName ) ) ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )? otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )? otherlv_6= RightParenthesis )
            {
            // InternalProblemParser.g:3741:2: ( ( ( ruleQualifiedName ) ) ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )? otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )? otherlv_6= RightParenthesis )
            // InternalProblemParser.g:3742:3: ( ( ruleQualifiedName ) ) ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )? otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )? otherlv_6= RightParenthesis
            {
            // InternalProblemParser.g:3742:3: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:3743:4: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:3743:4: ( ruleQualifiedName )
            // InternalProblemParser.g:3744:5: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getAtomRule());
              					}
              				
            }
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getAtomAccess().getRelationRelationCrossReference_0_0());
              				
            }
            pushFollow(FOLLOW_65);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:3758:3: ( (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE ) )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==RULE_TRANSITIVE_CLOSURE) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // InternalProblemParser.g:3759:4: (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE )
                    {
                    // InternalProblemParser.g:3759:4: (lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE )
                    // InternalProblemParser.g:3760:5: lv_transitiveClosure_1_0= RULE_TRANSITIVE_CLOSURE
                    {
                    lv_transitiveClosure_1_0=(Token)match(input,RULE_TRANSITIVE_CLOSURE,FOLLOW_21); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(lv_transitiveClosure_1_0, grammarAccess.getAtomAccess().getTransitiveClosureTRANSITIVE_CLOSURETerminalRuleCall_1_0());
                      				
                    }
                    if ( state.backtracking==0 ) {

                      					if (current==null) {
                      						current = createModelElement(grammarAccess.getAtomRule());
                      					}
                      					setWithLastConsumed(
                      						current,
                      						"transitiveClosure",
                      						lv_transitiveClosure_1_0 != null,
                      						"tools.refinery.language.Problem.TRANSITIVE_CLOSURE");
                      				
                    }

                    }


                    }
                    break;

            }

            otherlv_2=(Token)match(input,LeftParenthesis,FOLLOW_38); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_2, grammarAccess.getAtomAccess().getLeftParenthesisKeyword_2());
              		
            }
            // InternalProblemParser.g:3780:3: ( ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )* )?
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( ((LA79_0>=Concretization && LA79_0<=Primitive)||(LA79_0>=Contains && LA79_0<=Opposite)||(LA79_0>=Partial && LA79_0<=Assert)||LA79_0==Module||LA79_0==Shadow||(LA79_0>=Error && LA79_0<=Multi)||LA79_0==Atom||LA79_0==Must||LA79_0==True||LA79_0==May||LA79_0==ColonColon||LA79_0==As||LA79_0==ExclamationMark||LA79_0==LeftParenthesis||(LA79_0>=Asterisk && LA79_0<=PlusSign)||LA79_0==HyphenMinus||(LA79_0>=RULE_ID && LA79_0<=RULE_EXPONENTIAL)||(LA79_0>=RULE_STRING && LA79_0<=RULE_QUOTED_ID)) ) {
                alt79=1;
            }
            switch (alt79) {
                case 1 :
                    // InternalProblemParser.g:3781:4: ( (lv_arguments_3_0= ruleExpr ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )*
                    {
                    // InternalProblemParser.g:3781:4: ( (lv_arguments_3_0= ruleExpr ) )
                    // InternalProblemParser.g:3782:5: (lv_arguments_3_0= ruleExpr )
                    {
                    // InternalProblemParser.g:3782:5: (lv_arguments_3_0= ruleExpr )
                    // InternalProblemParser.g:3783:6: lv_arguments_3_0= ruleExpr
                    {
                    if ( state.backtracking==0 ) {

                      						newCompositeNode(grammarAccess.getAtomAccess().getArgumentsExprParserRuleCall_3_0_0());
                      					
                    }
                    pushFollow(FOLLOW_23);
                    lv_arguments_3_0=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElementForParent(grammarAccess.getAtomRule());
                      						}
                      						add(
                      							current,
                      							"arguments",
                      							lv_arguments_3_0,
                      							"tools.refinery.language.Problem.Expr");
                      						afterParserOrEnumRuleCall();
                      					
                    }

                    }


                    }

                    // InternalProblemParser.g:3800:4: (otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) ) )*
                    loop78:
                    do {
                        int alt78=2;
                        int LA78_0 = input.LA(1);

                        if ( (LA78_0==Comma) ) {
                            alt78=1;
                        }


                        switch (alt78) {
                    	case 1 :
                    	    // InternalProblemParser.g:3801:5: otherlv_4= Comma ( (lv_arguments_5_0= ruleExpr ) )
                    	    {
                    	    otherlv_4=(Token)match(input,Comma,FOLLOW_28); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      					newLeafNode(otherlv_4, grammarAccess.getAtomAccess().getCommaKeyword_3_1_0());
                    	      				
                    	    }
                    	    // InternalProblemParser.g:3805:5: ( (lv_arguments_5_0= ruleExpr ) )
                    	    // InternalProblemParser.g:3806:6: (lv_arguments_5_0= ruleExpr )
                    	    {
                    	    // InternalProblemParser.g:3806:6: (lv_arguments_5_0= ruleExpr )
                    	    // InternalProblemParser.g:3807:7: lv_arguments_5_0= ruleExpr
                    	    {
                    	    if ( state.backtracking==0 ) {

                    	      							newCompositeNode(grammarAccess.getAtomAccess().getArgumentsExprParserRuleCall_3_1_1_0());
                    	      						
                    	    }
                    	    pushFollow(FOLLOW_23);
                    	    lv_arguments_5_0=ruleExpr();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      							if (current==null) {
                    	      								current = createModelElementForParent(grammarAccess.getAtomRule());
                    	      							}
                    	      							add(
                    	      								current,
                    	      								"arguments",
                    	      								lv_arguments_5_0,
                    	      								"tools.refinery.language.Problem.Expr");
                    	      							afterParserOrEnumRuleCall();
                    	      						
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop78;
                        }
                    } while (true);


                    }
                    break;

            }

            otherlv_6=(Token)match(input,RightParenthesis,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_6, grammarAccess.getAtomAccess().getRightParenthesisKeyword_4());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAtom"


    // $ANTLR start "entryRuleVariableOrNodeExpr"
    // InternalProblemParser.g:3834:1: entryRuleVariableOrNodeExpr returns [EObject current=null] : iv_ruleVariableOrNodeExpr= ruleVariableOrNodeExpr EOF ;
    public final EObject entryRuleVariableOrNodeExpr() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleVariableOrNodeExpr = null;


        try {
            // InternalProblemParser.g:3834:59: (iv_ruleVariableOrNodeExpr= ruleVariableOrNodeExpr EOF )
            // InternalProblemParser.g:3835:2: iv_ruleVariableOrNodeExpr= ruleVariableOrNodeExpr EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getVariableOrNodeExprRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleVariableOrNodeExpr=ruleVariableOrNodeExpr();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleVariableOrNodeExpr; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleVariableOrNodeExpr"


    // $ANTLR start "ruleVariableOrNodeExpr"
    // InternalProblemParser.g:3841:1: ruleVariableOrNodeExpr returns [EObject current=null] : ( ( ruleQualifiedName ) ) ;
    public final EObject ruleVariableOrNodeExpr() throws RecognitionException {
        EObject current = null;


        	enterRule();

        try {
            // InternalProblemParser.g:3847:2: ( ( ( ruleQualifiedName ) ) )
            // InternalProblemParser.g:3848:2: ( ( ruleQualifiedName ) )
            {
            // InternalProblemParser.g:3848:2: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:3849:3: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:3849:3: ( ruleQualifiedName )
            // InternalProblemParser.g:3850:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElement(grammarAccess.getVariableOrNodeExprRule());
              				}
              			
            }
            if ( state.backtracking==0 ) {

              				newCompositeNode(grammarAccess.getVariableOrNodeExprAccess().getElementNamedElementCrossReference_0());
              			
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				afterParserOrEnumRuleCall();
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleVariableOrNodeExpr"


    // $ANTLR start "entryRuleConstant"
    // InternalProblemParser.g:3867:1: entryRuleConstant returns [EObject current=null] : iv_ruleConstant= ruleConstant EOF ;
    public final EObject entryRuleConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConstant = null;


        try {
            // InternalProblemParser.g:3867:49: (iv_ruleConstant= ruleConstant EOF )
            // InternalProblemParser.g:3868:2: iv_ruleConstant= ruleConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleConstant=ruleConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleConstant"


    // $ANTLR start "ruleConstant"
    // InternalProblemParser.g:3874:1: ruleConstant returns [EObject current=null] : (this_RealConstant_0= ruleRealConstant | this_IntConstant_1= ruleIntConstant | this_StringConstant_2= ruleStringConstant | this_InfiniteConstant_3= ruleInfiniteConstant | this_LogicConstant_4= ruleLogicConstant ) ;
    public final EObject ruleConstant() throws RecognitionException {
        EObject current = null;

        EObject this_RealConstant_0 = null;

        EObject this_IntConstant_1 = null;

        EObject this_StringConstant_2 = null;

        EObject this_InfiniteConstant_3 = null;

        EObject this_LogicConstant_4 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3880:2: ( (this_RealConstant_0= ruleRealConstant | this_IntConstant_1= ruleIntConstant | this_StringConstant_2= ruleStringConstant | this_InfiniteConstant_3= ruleInfiniteConstant | this_LogicConstant_4= ruleLogicConstant ) )
            // InternalProblemParser.g:3881:2: (this_RealConstant_0= ruleRealConstant | this_IntConstant_1= ruleIntConstant | this_StringConstant_2= ruleStringConstant | this_InfiniteConstant_3= ruleInfiniteConstant | this_LogicConstant_4= ruleLogicConstant )
            {
            // InternalProblemParser.g:3881:2: (this_RealConstant_0= ruleRealConstant | this_IntConstant_1= ruleIntConstant | this_StringConstant_2= ruleStringConstant | this_InfiniteConstant_3= ruleInfiniteConstant | this_LogicConstant_4= ruleLogicConstant )
            int alt80=5;
            switch ( input.LA(1) ) {
            case RULE_EXPONENTIAL:
                {
                alt80=1;
                }
                break;
            case RULE_INT:
                {
                int LA80_2 = input.LA(2);

                if ( (LA80_2==EOF||LA80_2==ExclamationMarkEqualsSignEqualsSign||(LA80_2>=EqualsSignEqualsSignEqualsSign && LA80_2<=EqualsSignEqualsSignGreaterThanSign)||(LA80_2>=ExclamationMarkEqualsSign && LA80_2<=AsteriskAsterisk)||(LA80_2>=HyphenMinusGreaterThanSign && LA80_2<=SolidusReverseSolidus)||(LA80_2>=ColonGreaterThanSign && LA80_2<=CircumflexAccentCircumflexAccent)||(LA80_2>=Is && LA80_2<=VerticalLineVerticalLine)||(LA80_2>=RightParenthesis && LA80_2<=HyphenMinus)||LA80_2==Solidus||(LA80_2>=Semicolon && LA80_2<=LessThanSign)||LA80_2==GreaterThanSign||LA80_2==RightCurlyBracket) ) {
                    alt80=2;
                }
                else if ( (LA80_2==FullStop) ) {
                    int LA80_7 = input.LA(3);

                    if ( ((LA80_7>=RULE_INT && LA80_7<=RULE_EXPONENTIAL)) ) {
                        alt80=1;
                    }
                    else if ( (LA80_7==EOF||(LA80_7>=Concretization && LA80_7<=Aggregator)||(LA80_7>=Container && LA80_7<=Default)||(LA80_7>=Problem && LA80_7<=Subsets)||(LA80_7>=Assert && LA80_7<=Module)||(LA80_7>=Shadow && LA80_7<=Error)||(LA80_7>=Multi && LA80_7<=Enum)||(LA80_7>=Pred && LA80_7<=Rule)||LA80_7==ColonColon||LA80_7==As||(LA80_7>=ExclamationMark && LA80_7<=NumberSign)||(LA80_7>=QuestionMark && LA80_7<=CommercialAt)||LA80_7==RULE_ID||LA80_7==RULE_QUOTED_ID) ) {
                        alt80=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 80, 7, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return current;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 80, 2, input);

                    throw nvae;
                }
                }
                break;
            case RULE_STRING:
                {
                alt80=3;
                }
                break;
            case Asterisk:
                {
                alt80=4;
                }
                break;
            case Unknown:
            case Error:
            case False:
            case True:
                {
                alt80=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 80, 0, input);

                throw nvae;
            }

            switch (alt80) {
                case 1 :
                    // InternalProblemParser.g:3882:3: this_RealConstant_0= ruleRealConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getConstantAccess().getRealConstantParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_RealConstant_0=ruleRealConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_RealConstant_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:3891:3: this_IntConstant_1= ruleIntConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getConstantAccess().getIntConstantParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_IntConstant_1=ruleIntConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_IntConstant_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:3900:3: this_StringConstant_2= ruleStringConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getConstantAccess().getStringConstantParserRuleCall_2());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_StringConstant_2=ruleStringConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_StringConstant_2;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:3909:3: this_InfiniteConstant_3= ruleInfiniteConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getConstantAccess().getInfiniteConstantParserRuleCall_3());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_InfiniteConstant_3=ruleInfiniteConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_InfiniteConstant_3;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:3918:3: this_LogicConstant_4= ruleLogicConstant
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getConstantAccess().getLogicConstantParserRuleCall_4());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_LogicConstant_4=ruleLogicConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_LogicConstant_4;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleConstant"


    // $ANTLR start "entryRuleIntConstant"
    // InternalProblemParser.g:3930:1: entryRuleIntConstant returns [EObject current=null] : iv_ruleIntConstant= ruleIntConstant EOF ;
    public final EObject entryRuleIntConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleIntConstant = null;


        try {
            // InternalProblemParser.g:3930:52: (iv_ruleIntConstant= ruleIntConstant EOF )
            // InternalProblemParser.g:3931:2: iv_ruleIntConstant= ruleIntConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIntConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleIntConstant=ruleIntConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleIntConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleIntConstant"


    // $ANTLR start "ruleIntConstant"
    // InternalProblemParser.g:3937:1: ruleIntConstant returns [EObject current=null] : ( (lv_intValue_0_0= ruleInteger ) ) ;
    public final EObject ruleIntConstant() throws RecognitionException {
        EObject current = null;

        AntlrDatatypeRuleToken lv_intValue_0_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3943:2: ( ( (lv_intValue_0_0= ruleInteger ) ) )
            // InternalProblemParser.g:3944:2: ( (lv_intValue_0_0= ruleInteger ) )
            {
            // InternalProblemParser.g:3944:2: ( (lv_intValue_0_0= ruleInteger ) )
            // InternalProblemParser.g:3945:3: (lv_intValue_0_0= ruleInteger )
            {
            // InternalProblemParser.g:3945:3: (lv_intValue_0_0= ruleInteger )
            // InternalProblemParser.g:3946:4: lv_intValue_0_0= ruleInteger
            {
            if ( state.backtracking==0 ) {

              				newCompositeNode(grammarAccess.getIntConstantAccess().getIntValueIntegerParserRuleCall_0());
              			
            }
            pushFollow(FOLLOW_2);
            lv_intValue_0_0=ruleInteger();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElementForParent(grammarAccess.getIntConstantRule());
              				}
              				set(
              					current,
              					"intValue",
              					lv_intValue_0_0,
              					"tools.refinery.language.Problem.Integer");
              				afterParserOrEnumRuleCall();
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleIntConstant"


    // $ANTLR start "entryRuleRealConstant"
    // InternalProblemParser.g:3966:1: entryRuleRealConstant returns [EObject current=null] : iv_ruleRealConstant= ruleRealConstant EOF ;
    public final EObject entryRuleRealConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRealConstant = null;


        try {
            // InternalProblemParser.g:3966:53: (iv_ruleRealConstant= ruleRealConstant EOF )
            // InternalProblemParser.g:3967:2: iv_ruleRealConstant= ruleRealConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getRealConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleRealConstant=ruleRealConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleRealConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleRealConstant"


    // $ANTLR start "ruleRealConstant"
    // InternalProblemParser.g:3973:1: ruleRealConstant returns [EObject current=null] : ( (lv_realValue_0_0= ruleReal ) ) ;
    public final EObject ruleRealConstant() throws RecognitionException {
        EObject current = null;

        AntlrDatatypeRuleToken lv_realValue_0_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:3979:2: ( ( (lv_realValue_0_0= ruleReal ) ) )
            // InternalProblemParser.g:3980:2: ( (lv_realValue_0_0= ruleReal ) )
            {
            // InternalProblemParser.g:3980:2: ( (lv_realValue_0_0= ruleReal ) )
            // InternalProblemParser.g:3981:3: (lv_realValue_0_0= ruleReal )
            {
            // InternalProblemParser.g:3981:3: (lv_realValue_0_0= ruleReal )
            // InternalProblemParser.g:3982:4: lv_realValue_0_0= ruleReal
            {
            if ( state.backtracking==0 ) {

              				newCompositeNode(grammarAccess.getRealConstantAccess().getRealValueRealParserRuleCall_0());
              			
            }
            pushFollow(FOLLOW_2);
            lv_realValue_0_0=ruleReal();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElementForParent(grammarAccess.getRealConstantRule());
              				}
              				set(
              					current,
              					"realValue",
              					lv_realValue_0_0,
              					"tools.refinery.language.Problem.Real");
              				afterParserOrEnumRuleCall();
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleRealConstant"


    // $ANTLR start "entryRuleStringConstant"
    // InternalProblemParser.g:4002:1: entryRuleStringConstant returns [EObject current=null] : iv_ruleStringConstant= ruleStringConstant EOF ;
    public final EObject entryRuleStringConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStringConstant = null;


        try {
            // InternalProblemParser.g:4002:55: (iv_ruleStringConstant= ruleStringConstant EOF )
            // InternalProblemParser.g:4003:2: iv_ruleStringConstant= ruleStringConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStringConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleStringConstant=ruleStringConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStringConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleStringConstant"


    // $ANTLR start "ruleStringConstant"
    // InternalProblemParser.g:4009:1: ruleStringConstant returns [EObject current=null] : ( (lv_stringValue_0_0= RULE_STRING ) ) ;
    public final EObject ruleStringConstant() throws RecognitionException {
        EObject current = null;

        Token lv_stringValue_0_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:4015:2: ( ( (lv_stringValue_0_0= RULE_STRING ) ) )
            // InternalProblemParser.g:4016:2: ( (lv_stringValue_0_0= RULE_STRING ) )
            {
            // InternalProblemParser.g:4016:2: ( (lv_stringValue_0_0= RULE_STRING ) )
            // InternalProblemParser.g:4017:3: (lv_stringValue_0_0= RULE_STRING )
            {
            // InternalProblemParser.g:4017:3: (lv_stringValue_0_0= RULE_STRING )
            // InternalProblemParser.g:4018:4: lv_stringValue_0_0= RULE_STRING
            {
            lv_stringValue_0_0=(Token)match(input,RULE_STRING,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				newLeafNode(lv_stringValue_0_0, grammarAccess.getStringConstantAccess().getStringValueSTRINGTerminalRuleCall_0());
              			
            }
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElement(grammarAccess.getStringConstantRule());
              				}
              				setWithLastConsumed(
              					current,
              					"stringValue",
              					lv_stringValue_0_0,
              					"tools.refinery.language.Problem.STRING");
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleStringConstant"


    // $ANTLR start "entryRuleInfiniteConstant"
    // InternalProblemParser.g:4037:1: entryRuleInfiniteConstant returns [EObject current=null] : iv_ruleInfiniteConstant= ruleInfiniteConstant EOF ;
    public final EObject entryRuleInfiniteConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleInfiniteConstant = null;


        try {
            // InternalProblemParser.g:4037:57: (iv_ruleInfiniteConstant= ruleInfiniteConstant EOF )
            // InternalProblemParser.g:4038:2: iv_ruleInfiniteConstant= ruleInfiniteConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getInfiniteConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleInfiniteConstant=ruleInfiniteConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleInfiniteConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleInfiniteConstant"


    // $ANTLR start "ruleInfiniteConstant"
    // InternalProblemParser.g:4044:1: ruleInfiniteConstant returns [EObject current=null] : ( () otherlv_1= Asterisk ) ;
    public final EObject ruleInfiniteConstant() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:4050:2: ( ( () otherlv_1= Asterisk ) )
            // InternalProblemParser.g:4051:2: ( () otherlv_1= Asterisk )
            {
            // InternalProblemParser.g:4051:2: ( () otherlv_1= Asterisk )
            // InternalProblemParser.g:4052:3: () otherlv_1= Asterisk
            {
            // InternalProblemParser.g:4052:3: ()
            // InternalProblemParser.g:4053:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getInfiniteConstantAccess().getInfiniteConstantAction_0(),
              					current);
              			
            }

            }

            otherlv_1=(Token)match(input,Asterisk,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_1, grammarAccess.getInfiniteConstantAccess().getAsteriskKeyword_1());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleInfiniteConstant"


    // $ANTLR start "entryRuleLogicConstant"
    // InternalProblemParser.g:4067:1: entryRuleLogicConstant returns [EObject current=null] : iv_ruleLogicConstant= ruleLogicConstant EOF ;
    public final EObject entryRuleLogicConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleLogicConstant = null;


        try {
            // InternalProblemParser.g:4067:54: (iv_ruleLogicConstant= ruleLogicConstant EOF )
            // InternalProblemParser.g:4068:2: iv_ruleLogicConstant= ruleLogicConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getLogicConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleLogicConstant=ruleLogicConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleLogicConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleLogicConstant"


    // $ANTLR start "ruleLogicConstant"
    // InternalProblemParser.g:4074:1: ruleLogicConstant returns [EObject current=null] : ( (lv_logicValue_0_0= ruleLogicValue ) ) ;
    public final EObject ruleLogicConstant() throws RecognitionException {
        EObject current = null;

        Enumerator lv_logicValue_0_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4080:2: ( ( (lv_logicValue_0_0= ruleLogicValue ) ) )
            // InternalProblemParser.g:4081:2: ( (lv_logicValue_0_0= ruleLogicValue ) )
            {
            // InternalProblemParser.g:4081:2: ( (lv_logicValue_0_0= ruleLogicValue ) )
            // InternalProblemParser.g:4082:3: (lv_logicValue_0_0= ruleLogicValue )
            {
            // InternalProblemParser.g:4082:3: (lv_logicValue_0_0= ruleLogicValue )
            // InternalProblemParser.g:4083:4: lv_logicValue_0_0= ruleLogicValue
            {
            if ( state.backtracking==0 ) {

              				newCompositeNode(grammarAccess.getLogicConstantAccess().getLogicValueLogicValueEnumRuleCall_0());
              			
            }
            pushFollow(FOLLOW_2);
            lv_logicValue_0_0=ruleLogicValue();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElementForParent(grammarAccess.getLogicConstantRule());
              				}
              				set(
              					current,
              					"logicValue",
              					lv_logicValue_0_0,
              					"tools.refinery.language.Problem.LogicValue");
              				afterParserOrEnumRuleCall();
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleLogicConstant"


    // $ANTLR start "entryRuleAssertion"
    // InternalProblemParser.g:4103:1: entryRuleAssertion returns [EObject current=null] : iv_ruleAssertion= ruleAssertion EOF ;
    public final EObject entryRuleAssertion() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAssertion = null;


        try {
            // InternalProblemParser.g:4103:50: (iv_ruleAssertion= ruleAssertion EOF )
            // InternalProblemParser.g:4104:2: iv_ruleAssertion= ruleAssertion EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAssertionRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAssertion=ruleAssertion();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAssertion; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAssertion"


    // $ANTLR start "ruleAssertion"
    // InternalProblemParser.g:4110:1: ruleAssertion returns [EObject current=null] : ( ( (lv_default_0_0= Default ) )? ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) ) otherlv_16= FullStop ) ;
    public final EObject ruleAssertion() throws RecognitionException {
        EObject current = null;

        Token lv_default_0_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        Token otherlv_7=null;
        Token otherlv_11=null;
        Token otherlv_13=null;
        Token otherlv_15=null;
        Token otherlv_16=null;
        EObject lv_arguments_3_0 = null;

        EObject lv_arguments_5_0 = null;

        EObject lv_value_8_0 = null;

        EObject lv_value_9_0 = null;

        EObject lv_arguments_12_0 = null;

        EObject lv_arguments_14_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4116:2: ( ( ( (lv_default_0_0= Default ) )? ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) ) otherlv_16= FullStop ) )
            // InternalProblemParser.g:4117:2: ( ( (lv_default_0_0= Default ) )? ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) ) otherlv_16= FullStop )
            {
            // InternalProblemParser.g:4117:2: ( ( (lv_default_0_0= Default ) )? ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) ) otherlv_16= FullStop )
            // InternalProblemParser.g:4118:3: ( (lv_default_0_0= Default ) )? ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) ) otherlv_16= FullStop
            {
            // InternalProblemParser.g:4118:3: ( (lv_default_0_0= Default ) )?
            int alt81=2;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==Default) ) {
                alt81=1;
            }
            switch (alt81) {
                case 1 :
                    // InternalProblemParser.g:4119:4: (lv_default_0_0= Default )
                    {
                    // InternalProblemParser.g:4119:4: (lv_default_0_0= Default )
                    // InternalProblemParser.g:4120:5: lv_default_0_0= Default
                    {
                    lv_default_0_0=(Token)match(input,Default,FOLLOW_34); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(lv_default_0_0, grammarAccess.getAssertionAccess().getDefaultDefaultKeyword_0_0());
                      				
                    }
                    if ( state.backtracking==0 ) {

                      					if (current==null) {
                      						current = createModelElement(grammarAccess.getAssertionRule());
                      					}
                      					setWithLastConsumed(current, "default", lv_default_0_0 != null, "default");
                      				
                    }

                    }


                    }
                    break;

            }

            // InternalProblemParser.g:4132:3: ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) )
            int alt86=2;
            alt86 = dfa86.predict(input);
            switch (alt86) {
                case 1 :
                    // InternalProblemParser.g:4133:4: ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) )
                    {
                    // InternalProblemParser.g:4133:4: ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) )
                    // InternalProblemParser.g:4134:5: ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) )
                    {
                    // InternalProblemParser.g:4134:5: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:4135:6: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:4135:6: ( ruleQualifiedName )
                    // InternalProblemParser.g:4136:7: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElement(grammarAccess.getAssertionRule());
                      							}
                      						
                    }
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAssertionAccess().getRelationRelationCrossReference_1_0_0_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_2=(Token)match(input,LeftParenthesis,FOLLOW_51); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_2, grammarAccess.getAssertionAccess().getLeftParenthesisKeyword_1_0_1());
                      				
                    }
                    // InternalProblemParser.g:4154:5: ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )?
                    int alt83=2;
                    int LA83_0 = input.LA(1);

                    if ( ((LA83_0>=Concretization && LA83_0<=Aggregator)||(LA83_0>=Container && LA83_0<=Primitive)||(LA83_0>=Contains && LA83_0<=Opposite)||(LA83_0>=Problem && LA83_0<=Subsets)||LA83_0==Assert||LA83_0==Module||LA83_0==Shadow||LA83_0==Multi||LA83_0==Atom||LA83_0==ColonColon||LA83_0==As||LA83_0==Asterisk||LA83_0==RULE_ID||LA83_0==RULE_QUOTED_ID) ) {
                        alt83=1;
                    }
                    switch (alt83) {
                        case 1 :
                            // InternalProblemParser.g:4155:6: ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )*
                            {
                            // InternalProblemParser.g:4155:6: ( (lv_arguments_3_0= ruleAssertionArgument ) )
                            // InternalProblemParser.g:4156:7: (lv_arguments_3_0= ruleAssertionArgument )
                            {
                            // InternalProblemParser.g:4156:7: (lv_arguments_3_0= ruleAssertionArgument )
                            // InternalProblemParser.g:4157:8: lv_arguments_3_0= ruleAssertionArgument
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAssertionAccess().getArgumentsAssertionArgumentParserRuleCall_1_0_2_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_arguments_3_0=ruleAssertionArgument();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAssertionRule());
                              								}
                              								add(
                              									current,
                              									"arguments",
                              									lv_arguments_3_0,
                              									"tools.refinery.language.Problem.AssertionArgument");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:4174:6: (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )*
                            loop82:
                            do {
                                int alt82=2;
                                int LA82_0 = input.LA(1);

                                if ( (LA82_0==Comma) ) {
                                    alt82=1;
                                }


                                switch (alt82) {
                            	case 1 :
                            	    // InternalProblemParser.g:4175:7: otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) )
                            	    {
                            	    otherlv_4=(Token)match(input,Comma,FOLLOW_52); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_4, grammarAccess.getAssertionAccess().getCommaKeyword_1_0_2_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:4179:7: ( (lv_arguments_5_0= ruleAssertionArgument ) )
                            	    // InternalProblemParser.g:4180:8: (lv_arguments_5_0= ruleAssertionArgument )
                            	    {
                            	    // InternalProblemParser.g:4180:8: (lv_arguments_5_0= ruleAssertionArgument )
                            	    // InternalProblemParser.g:4181:9: lv_arguments_5_0= ruleAssertionArgument
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAssertionAccess().getArgumentsAssertionArgumentParserRuleCall_1_0_2_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_arguments_5_0=ruleAssertionArgument();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAssertionRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"arguments",
                            	      										lv_arguments_5_0,
                            	      										"tools.refinery.language.Problem.AssertionArgument");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop82;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_6=(Token)match(input,RightParenthesis,FOLLOW_53); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_6, grammarAccess.getAssertionAccess().getRightParenthesisKeyword_1_0_3());
                      				
                    }
                    otherlv_7=(Token)match(input,Colon,FOLLOW_28); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_7, grammarAccess.getAssertionAccess().getColonKeyword_1_0_4());
                      				
                    }
                    // InternalProblemParser.g:4208:5: ( (lv_value_8_0= ruleExpr ) )
                    // InternalProblemParser.g:4209:6: (lv_value_8_0= ruleExpr )
                    {
                    // InternalProblemParser.g:4209:6: (lv_value_8_0= ruleExpr )
                    // InternalProblemParser.g:4210:7: lv_value_8_0= ruleExpr
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAssertionAccess().getValueExprParserRuleCall_1_0_5_0());
                      						
                    }
                    pushFollow(FOLLOW_4);
                    lv_value_8_0=ruleExpr();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAssertionRule());
                      							}
                      							set(
                      								current,
                      								"value",
                      								lv_value_8_0,
                      								"tools.refinery.language.Problem.Expr");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4229:4: ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis )
                    {
                    // InternalProblemParser.g:4229:4: ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis )
                    // InternalProblemParser.g:4230:5: ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis
                    {
                    // InternalProblemParser.g:4230:5: ( (lv_value_9_0= ruleShortLogicConstant ) )
                    // InternalProblemParser.g:4231:6: (lv_value_9_0= ruleShortLogicConstant )
                    {
                    // InternalProblemParser.g:4231:6: (lv_value_9_0= ruleShortLogicConstant )
                    // InternalProblemParser.g:4232:7: lv_value_9_0= ruleShortLogicConstant
                    {
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAssertionAccess().getValueShortLogicConstantParserRuleCall_1_1_0_0());
                      						
                    }
                    pushFollow(FOLLOW_8);
                    lv_value_9_0=ruleShortLogicConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElementForParent(grammarAccess.getAssertionRule());
                      							}
                      							set(
                      								current,
                      								"value",
                      								lv_value_9_0,
                      								"tools.refinery.language.Problem.ShortLogicConstant");
                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    // InternalProblemParser.g:4249:5: ( ( ruleQualifiedName ) )
                    // InternalProblemParser.g:4250:6: ( ruleQualifiedName )
                    {
                    // InternalProblemParser.g:4250:6: ( ruleQualifiedName )
                    // InternalProblemParser.g:4251:7: ruleQualifiedName
                    {
                    if ( state.backtracking==0 ) {

                      							if (current==null) {
                      								current = createModelElement(grammarAccess.getAssertionRule());
                      							}
                      						
                    }
                    if ( state.backtracking==0 ) {

                      							newCompositeNode(grammarAccess.getAssertionAccess().getRelationRelationCrossReference_1_1_1_0());
                      						
                    }
                    pushFollow(FOLLOW_21);
                    ruleQualifiedName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      							afterParserOrEnumRuleCall();
                      						
                    }

                    }


                    }

                    otherlv_11=(Token)match(input,LeftParenthesis,FOLLOW_51); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_11, grammarAccess.getAssertionAccess().getLeftParenthesisKeyword_1_1_2());
                      				
                    }
                    // InternalProblemParser.g:4269:5: ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )?
                    int alt85=2;
                    int LA85_0 = input.LA(1);

                    if ( ((LA85_0>=Concretization && LA85_0<=Aggregator)||(LA85_0>=Container && LA85_0<=Primitive)||(LA85_0>=Contains && LA85_0<=Opposite)||(LA85_0>=Problem && LA85_0<=Subsets)||LA85_0==Assert||LA85_0==Module||LA85_0==Shadow||LA85_0==Multi||LA85_0==Atom||LA85_0==ColonColon||LA85_0==As||LA85_0==Asterisk||LA85_0==RULE_ID||LA85_0==RULE_QUOTED_ID) ) {
                        alt85=1;
                    }
                    switch (alt85) {
                        case 1 :
                            // InternalProblemParser.g:4270:6: ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )*
                            {
                            // InternalProblemParser.g:4270:6: ( (lv_arguments_12_0= ruleAssertionArgument ) )
                            // InternalProblemParser.g:4271:7: (lv_arguments_12_0= ruleAssertionArgument )
                            {
                            // InternalProblemParser.g:4271:7: (lv_arguments_12_0= ruleAssertionArgument )
                            // InternalProblemParser.g:4272:8: lv_arguments_12_0= ruleAssertionArgument
                            {
                            if ( state.backtracking==0 ) {

                              								newCompositeNode(grammarAccess.getAssertionAccess().getArgumentsAssertionArgumentParserRuleCall_1_1_3_0_0());
                              							
                            }
                            pushFollow(FOLLOW_23);
                            lv_arguments_12_0=ruleAssertionArgument();

                            state._fsp--;
                            if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              								if (current==null) {
                              									current = createModelElementForParent(grammarAccess.getAssertionRule());
                              								}
                              								add(
                              									current,
                              									"arguments",
                              									lv_arguments_12_0,
                              									"tools.refinery.language.Problem.AssertionArgument");
                              								afterParserOrEnumRuleCall();
                              							
                            }

                            }


                            }

                            // InternalProblemParser.g:4289:6: (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )*
                            loop84:
                            do {
                                int alt84=2;
                                int LA84_0 = input.LA(1);

                                if ( (LA84_0==Comma) ) {
                                    alt84=1;
                                }


                                switch (alt84) {
                            	case 1 :
                            	    // InternalProblemParser.g:4290:7: otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) )
                            	    {
                            	    otherlv_13=(Token)match(input,Comma,FOLLOW_52); if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      							newLeafNode(otherlv_13, grammarAccess.getAssertionAccess().getCommaKeyword_1_1_3_1_0());
                            	      						
                            	    }
                            	    // InternalProblemParser.g:4294:7: ( (lv_arguments_14_0= ruleAssertionArgument ) )
                            	    // InternalProblemParser.g:4295:8: (lv_arguments_14_0= ruleAssertionArgument )
                            	    {
                            	    // InternalProblemParser.g:4295:8: (lv_arguments_14_0= ruleAssertionArgument )
                            	    // InternalProblemParser.g:4296:9: lv_arguments_14_0= ruleAssertionArgument
                            	    {
                            	    if ( state.backtracking==0 ) {

                            	      									newCompositeNode(grammarAccess.getAssertionAccess().getArgumentsAssertionArgumentParserRuleCall_1_1_3_1_1_0());
                            	      								
                            	    }
                            	    pushFollow(FOLLOW_23);
                            	    lv_arguments_14_0=ruleAssertionArgument();

                            	    state._fsp--;
                            	    if (state.failed) return current;
                            	    if ( state.backtracking==0 ) {

                            	      									if (current==null) {
                            	      										current = createModelElementForParent(grammarAccess.getAssertionRule());
                            	      									}
                            	      									add(
                            	      										current,
                            	      										"arguments",
                            	      										lv_arguments_14_0,
                            	      										"tools.refinery.language.Problem.AssertionArgument");
                            	      									afterParserOrEnumRuleCall();
                            	      								
                            	    }

                            	    }


                            	    }


                            	    }
                            	    break;

                            	default :
                            	    break loop84;
                                }
                            } while (true);


                            }
                            break;

                    }

                    otherlv_15=(Token)match(input,RightParenthesis,FOLLOW_4); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					newLeafNode(otherlv_15, grammarAccess.getAssertionAccess().getRightParenthesisKeyword_1_1_4());
                      				
                    }

                    }


                    }
                    break;

            }

            otherlv_16=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_16, grammarAccess.getAssertionAccess().getFullStopKeyword_2());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAssertion"


    // $ANTLR start "entryRuleAssertionArgument"
    // InternalProblemParser.g:4329:1: entryRuleAssertionArgument returns [EObject current=null] : iv_ruleAssertionArgument= ruleAssertionArgument EOF ;
    public final EObject entryRuleAssertionArgument() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAssertionArgument = null;


        try {
            // InternalProblemParser.g:4329:58: (iv_ruleAssertionArgument= ruleAssertionArgument EOF )
            // InternalProblemParser.g:4330:2: iv_ruleAssertionArgument= ruleAssertionArgument EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAssertionArgumentRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleAssertionArgument=ruleAssertionArgument();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAssertionArgument; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleAssertionArgument"


    // $ANTLR start "ruleAssertionArgument"
    // InternalProblemParser.g:4336:1: ruleAssertionArgument returns [EObject current=null] : (this_NodeAssertionArgument_0= ruleNodeAssertionArgument | this_WildcardAssertionArgument_1= ruleWildcardAssertionArgument ) ;
    public final EObject ruleAssertionArgument() throws RecognitionException {
        EObject current = null;

        EObject this_NodeAssertionArgument_0 = null;

        EObject this_WildcardAssertionArgument_1 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4342:2: ( (this_NodeAssertionArgument_0= ruleNodeAssertionArgument | this_WildcardAssertionArgument_1= ruleWildcardAssertionArgument ) )
            // InternalProblemParser.g:4343:2: (this_NodeAssertionArgument_0= ruleNodeAssertionArgument | this_WildcardAssertionArgument_1= ruleWildcardAssertionArgument )
            {
            // InternalProblemParser.g:4343:2: (this_NodeAssertionArgument_0= ruleNodeAssertionArgument | this_WildcardAssertionArgument_1= ruleWildcardAssertionArgument )
            int alt87=2;
            int LA87_0 = input.LA(1);

            if ( ((LA87_0>=Concretization && LA87_0<=Aggregator)||(LA87_0>=Container && LA87_0<=Primitive)||(LA87_0>=Contains && LA87_0<=Opposite)||(LA87_0>=Problem && LA87_0<=Subsets)||LA87_0==Assert||LA87_0==Module||LA87_0==Shadow||LA87_0==Multi||LA87_0==Atom||LA87_0==ColonColon||LA87_0==As||LA87_0==RULE_ID||LA87_0==RULE_QUOTED_ID) ) {
                alt87=1;
            }
            else if ( (LA87_0==Asterisk) ) {
                alt87=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 87, 0, input);

                throw nvae;
            }
            switch (alt87) {
                case 1 :
                    // InternalProblemParser.g:4344:3: this_NodeAssertionArgument_0= ruleNodeAssertionArgument
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getAssertionArgumentAccess().getNodeAssertionArgumentParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_NodeAssertionArgument_0=ruleNodeAssertionArgument();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_NodeAssertionArgument_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4353:3: this_WildcardAssertionArgument_1= ruleWildcardAssertionArgument
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getAssertionArgumentAccess().getWildcardAssertionArgumentParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_WildcardAssertionArgument_1=ruleWildcardAssertionArgument();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_WildcardAssertionArgument_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAssertionArgument"


    // $ANTLR start "entryRuleNodeAssertionArgument"
    // InternalProblemParser.g:4365:1: entryRuleNodeAssertionArgument returns [EObject current=null] : iv_ruleNodeAssertionArgument= ruleNodeAssertionArgument EOF ;
    public final EObject entryRuleNodeAssertionArgument() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNodeAssertionArgument = null;


        try {
            // InternalProblemParser.g:4365:62: (iv_ruleNodeAssertionArgument= ruleNodeAssertionArgument EOF )
            // InternalProblemParser.g:4366:2: iv_ruleNodeAssertionArgument= ruleNodeAssertionArgument EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNodeAssertionArgumentRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleNodeAssertionArgument=ruleNodeAssertionArgument();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNodeAssertionArgument; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleNodeAssertionArgument"


    // $ANTLR start "ruleNodeAssertionArgument"
    // InternalProblemParser.g:4372:1: ruleNodeAssertionArgument returns [EObject current=null] : ( ( ruleQualifiedName ) ) ;
    public final EObject ruleNodeAssertionArgument() throws RecognitionException {
        EObject current = null;


        	enterRule();

        try {
            // InternalProblemParser.g:4378:2: ( ( ( ruleQualifiedName ) ) )
            // InternalProblemParser.g:4379:2: ( ( ruleQualifiedName ) )
            {
            // InternalProblemParser.g:4379:2: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:4380:3: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:4380:3: ( ruleQualifiedName )
            // InternalProblemParser.g:4381:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElement(grammarAccess.getNodeAssertionArgumentRule());
              				}
              			
            }
            if ( state.backtracking==0 ) {

              				newCompositeNode(grammarAccess.getNodeAssertionArgumentAccess().getNodeNodeCrossReference_0());
              			
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				afterParserOrEnumRuleCall();
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleNodeAssertionArgument"


    // $ANTLR start "entryRuleWildcardAssertionArgument"
    // InternalProblemParser.g:4398:1: entryRuleWildcardAssertionArgument returns [EObject current=null] : iv_ruleWildcardAssertionArgument= ruleWildcardAssertionArgument EOF ;
    public final EObject entryRuleWildcardAssertionArgument() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleWildcardAssertionArgument = null;


        try {
            // InternalProblemParser.g:4398:66: (iv_ruleWildcardAssertionArgument= ruleWildcardAssertionArgument EOF )
            // InternalProblemParser.g:4399:2: iv_ruleWildcardAssertionArgument= ruleWildcardAssertionArgument EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getWildcardAssertionArgumentRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleWildcardAssertionArgument=ruleWildcardAssertionArgument();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleWildcardAssertionArgument; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleWildcardAssertionArgument"


    // $ANTLR start "ruleWildcardAssertionArgument"
    // InternalProblemParser.g:4405:1: ruleWildcardAssertionArgument returns [EObject current=null] : ( () otherlv_1= Asterisk ) ;
    public final EObject ruleWildcardAssertionArgument() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:4411:2: ( ( () otherlv_1= Asterisk ) )
            // InternalProblemParser.g:4412:2: ( () otherlv_1= Asterisk )
            {
            // InternalProblemParser.g:4412:2: ( () otherlv_1= Asterisk )
            // InternalProblemParser.g:4413:3: () otherlv_1= Asterisk
            {
            // InternalProblemParser.g:4413:3: ()
            // InternalProblemParser.g:4414:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getWildcardAssertionArgumentAccess().getWildcardAssertionArgumentAction_0(),
              					current);
              			
            }

            }

            otherlv_1=(Token)match(input,Asterisk,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_1, grammarAccess.getWildcardAssertionArgumentAccess().getAsteriskKeyword_1());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleWildcardAssertionArgument"


    // $ANTLR start "entryRuleShortLogicConstant"
    // InternalProblemParser.g:4428:1: entryRuleShortLogicConstant returns [EObject current=null] : iv_ruleShortLogicConstant= ruleShortLogicConstant EOF ;
    public final EObject entryRuleShortLogicConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleShortLogicConstant = null;


        try {
            // InternalProblemParser.g:4428:59: (iv_ruleShortLogicConstant= ruleShortLogicConstant EOF )
            // InternalProblemParser.g:4429:2: iv_ruleShortLogicConstant= ruleShortLogicConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getShortLogicConstantRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleShortLogicConstant=ruleShortLogicConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleShortLogicConstant; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleShortLogicConstant"


    // $ANTLR start "ruleShortLogicConstant"
    // InternalProblemParser.g:4435:1: ruleShortLogicConstant returns [EObject current=null] : ( () ( (lv_logicValue_1_0= ruleShortLogicValue ) )? ) ;
    public final EObject ruleShortLogicConstant() throws RecognitionException {
        EObject current = null;

        Enumerator lv_logicValue_1_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4441:2: ( ( () ( (lv_logicValue_1_0= ruleShortLogicValue ) )? ) )
            // InternalProblemParser.g:4442:2: ( () ( (lv_logicValue_1_0= ruleShortLogicValue ) )? )
            {
            // InternalProblemParser.g:4442:2: ( () ( (lv_logicValue_1_0= ruleShortLogicValue ) )? )
            // InternalProblemParser.g:4443:3: () ( (lv_logicValue_1_0= ruleShortLogicValue ) )?
            {
            // InternalProblemParser.g:4443:3: ()
            // InternalProblemParser.g:4444:4: 
            {
            if ( state.backtracking==0 ) {

              				current = forceCreateModelElement(
              					grammarAccess.getShortLogicConstantAccess().getLogicConstantAction_0(),
              					current);
              			
            }

            }

            // InternalProblemParser.g:4450:3: ( (lv_logicValue_1_0= ruleShortLogicValue ) )?
            int alt88=2;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==ExclamationMark||LA88_0==QuestionMark) ) {
                alt88=1;
            }
            switch (alt88) {
                case 1 :
                    // InternalProblemParser.g:4451:4: (lv_logicValue_1_0= ruleShortLogicValue )
                    {
                    // InternalProblemParser.g:4451:4: (lv_logicValue_1_0= ruleShortLogicValue )
                    // InternalProblemParser.g:4452:5: lv_logicValue_1_0= ruleShortLogicValue
                    {
                    if ( state.backtracking==0 ) {

                      					newCompositeNode(grammarAccess.getShortLogicConstantAccess().getLogicValueShortLogicValueEnumRuleCall_1_0());
                      				
                    }
                    pushFollow(FOLLOW_2);
                    lv_logicValue_1_0=ruleShortLogicValue();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					if (current==null) {
                      						current = createModelElementForParent(grammarAccess.getShortLogicConstantRule());
                      					}
                      					set(
                      						current,
                      						"logicValue",
                      						lv_logicValue_1_0,
                      						"tools.refinery.language.Problem.ShortLogicValue");
                      					afterParserOrEnumRuleCall();
                      				
                    }

                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleShortLogicConstant"


    // $ANTLR start "entryRuleScopeDeclaration"
    // InternalProblemParser.g:4473:1: entryRuleScopeDeclaration returns [EObject current=null] : iv_ruleScopeDeclaration= ruleScopeDeclaration EOF ;
    public final EObject entryRuleScopeDeclaration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleScopeDeclaration = null;


        try {
            // InternalProblemParser.g:4473:57: (iv_ruleScopeDeclaration= ruleScopeDeclaration EOF )
            // InternalProblemParser.g:4474:2: iv_ruleScopeDeclaration= ruleScopeDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getScopeDeclarationRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleScopeDeclaration=ruleScopeDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleScopeDeclaration; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleScopeDeclaration"


    // $ANTLR start "ruleScopeDeclaration"
    // InternalProblemParser.g:4480:1: ruleScopeDeclaration returns [EObject current=null] : (otherlv_0= Scope ( (lv_typeScopes_1_0= ruleTypeScope ) ) (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )* otherlv_4= FullStop ) ;
    public final EObject ruleScopeDeclaration() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        EObject lv_typeScopes_1_0 = null;

        EObject lv_typeScopes_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4486:2: ( (otherlv_0= Scope ( (lv_typeScopes_1_0= ruleTypeScope ) ) (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )* otherlv_4= FullStop ) )
            // InternalProblemParser.g:4487:2: (otherlv_0= Scope ( (lv_typeScopes_1_0= ruleTypeScope ) ) (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )* otherlv_4= FullStop )
            {
            // InternalProblemParser.g:4487:2: (otherlv_0= Scope ( (lv_typeScopes_1_0= ruleTypeScope ) ) (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )* otherlv_4= FullStop )
            // InternalProblemParser.g:4488:3: otherlv_0= Scope ( (lv_typeScopes_1_0= ruleTypeScope ) ) (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )* otherlv_4= FullStop
            {
            otherlv_0=(Token)match(input,Scope,FOLLOW_8); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_0, grammarAccess.getScopeDeclarationAccess().getScopeKeyword_0());
              		
            }
            // InternalProblemParser.g:4492:3: ( (lv_typeScopes_1_0= ruleTypeScope ) )
            // InternalProblemParser.g:4493:4: (lv_typeScopes_1_0= ruleTypeScope )
            {
            // InternalProblemParser.g:4493:4: (lv_typeScopes_1_0= ruleTypeScope )
            // InternalProblemParser.g:4494:5: lv_typeScopes_1_0= ruleTypeScope
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getScopeDeclarationAccess().getTypeScopesTypeScopeParserRuleCall_1_0());
              				
            }
            pushFollow(FOLLOW_35);
            lv_typeScopes_1_0=ruleTypeScope();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getScopeDeclarationRule());
              					}
              					add(
              						current,
              						"typeScopes",
              						lv_typeScopes_1_0,
              						"tools.refinery.language.Problem.TypeScope");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:4511:3: (otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) ) )*
            loop89:
            do {
                int alt89=2;
                int LA89_0 = input.LA(1);

                if ( (LA89_0==Comma) ) {
                    alt89=1;
                }


                switch (alt89) {
            	case 1 :
            	    // InternalProblemParser.g:4512:4: otherlv_2= Comma ( (lv_typeScopes_3_0= ruleTypeScope ) )
            	    {
            	    otherlv_2=(Token)match(input,Comma,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(otherlv_2, grammarAccess.getScopeDeclarationAccess().getCommaKeyword_2_0());
            	      			
            	    }
            	    // InternalProblemParser.g:4516:4: ( (lv_typeScopes_3_0= ruleTypeScope ) )
            	    // InternalProblemParser.g:4517:5: (lv_typeScopes_3_0= ruleTypeScope )
            	    {
            	    // InternalProblemParser.g:4517:5: (lv_typeScopes_3_0= ruleTypeScope )
            	    // InternalProblemParser.g:4518:6: lv_typeScopes_3_0= ruleTypeScope
            	    {
            	    if ( state.backtracking==0 ) {

            	      						newCompositeNode(grammarAccess.getScopeDeclarationAccess().getTypeScopesTypeScopeParserRuleCall_2_1_0());
            	      					
            	    }
            	    pushFollow(FOLLOW_35);
            	    lv_typeScopes_3_0=ruleTypeScope();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      						if (current==null) {
            	      							current = createModelElementForParent(grammarAccess.getScopeDeclarationRule());
            	      						}
            	      						add(
            	      							current,
            	      							"typeScopes",
            	      							lv_typeScopes_3_0,
            	      							"tools.refinery.language.Problem.TypeScope");
            	      						afterParserOrEnumRuleCall();
            	      					
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop89;
                }
            } while (true);

            otherlv_4=(Token)match(input,FullStop,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_4, grammarAccess.getScopeDeclarationAccess().getFullStopKeyword_3());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleScopeDeclaration"


    // $ANTLR start "entryRuleTypeScope"
    // InternalProblemParser.g:4544:1: entryRuleTypeScope returns [EObject current=null] : iv_ruleTypeScope= ruleTypeScope EOF ;
    public final EObject entryRuleTypeScope() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTypeScope = null;


        try {
            // InternalProblemParser.g:4544:50: (iv_ruleTypeScope= ruleTypeScope EOF )
            // InternalProblemParser.g:4545:2: iv_ruleTypeScope= ruleTypeScope EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTypeScopeRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleTypeScope=ruleTypeScope();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTypeScope; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleTypeScope"


    // $ANTLR start "ruleTypeScope"
    // InternalProblemParser.g:4551:1: ruleTypeScope returns [EObject current=null] : ( ( ( ruleQualifiedName ) ) ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign ) ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) ) ) ;
    public final EObject ruleTypeScope() throws RecognitionException {
        EObject current = null;

        Token lv_increment_1_0=null;
        Token otherlv_2=null;
        EObject lv_multiplicity_3_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4557:2: ( ( ( ( ruleQualifiedName ) ) ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign ) ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) ) ) )
            // InternalProblemParser.g:4558:2: ( ( ( ruleQualifiedName ) ) ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign ) ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) ) )
            {
            // InternalProblemParser.g:4558:2: ( ( ( ruleQualifiedName ) ) ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign ) ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) ) )
            // InternalProblemParser.g:4559:3: ( ( ruleQualifiedName ) ) ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign ) ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) )
            {
            // InternalProblemParser.g:4559:3: ( ( ruleQualifiedName ) )
            // InternalProblemParser.g:4560:4: ( ruleQualifiedName )
            {
            // InternalProblemParser.g:4560:4: ( ruleQualifiedName )
            // InternalProblemParser.g:4561:5: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getTypeScopeRule());
              					}
              				
            }
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getTypeScopeAccess().getTargetTypeRelationCrossReference_0_0());
              				
            }
            pushFollow(FOLLOW_66);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					afterParserOrEnumRuleCall();
              				
            }

            }


            }

            // InternalProblemParser.g:4575:3: ( ( (lv_increment_1_0= PlusSignEqualsSign ) ) | otherlv_2= EqualsSign )
            int alt90=2;
            int LA90_0 = input.LA(1);

            if ( (LA90_0==PlusSignEqualsSign) ) {
                alt90=1;
            }
            else if ( (LA90_0==EqualsSign) ) {
                alt90=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 90, 0, input);

                throw nvae;
            }
            switch (alt90) {
                case 1 :
                    // InternalProblemParser.g:4576:4: ( (lv_increment_1_0= PlusSignEqualsSign ) )
                    {
                    // InternalProblemParser.g:4576:4: ( (lv_increment_1_0= PlusSignEqualsSign ) )
                    // InternalProblemParser.g:4577:5: (lv_increment_1_0= PlusSignEqualsSign )
                    {
                    // InternalProblemParser.g:4577:5: (lv_increment_1_0= PlusSignEqualsSign )
                    // InternalProblemParser.g:4578:6: lv_increment_1_0= PlusSignEqualsSign
                    {
                    lv_increment_1_0=(Token)match(input,PlusSignEqualsSign,FOLLOW_46); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      						newLeafNode(lv_increment_1_0, grammarAccess.getTypeScopeAccess().getIncrementPlusSignEqualsSignKeyword_1_0_0());
                      					
                    }
                    if ( state.backtracking==0 ) {

                      						if (current==null) {
                      							current = createModelElement(grammarAccess.getTypeScopeRule());
                      						}
                      						setWithLastConsumed(current, "increment", lv_increment_1_0 != null, "+=");
                      					
                    }

                    }


                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4591:4: otherlv_2= EqualsSign
                    {
                    otherlv_2=(Token)match(input,EqualsSign,FOLLOW_46); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				newLeafNode(otherlv_2, grammarAccess.getTypeScopeAccess().getEqualsSignKeyword_1_1());
                      			
                    }

                    }
                    break;

            }

            // InternalProblemParser.g:4596:3: ( (lv_multiplicity_3_0= ruleDefiniteMultiplicity ) )
            // InternalProblemParser.g:4597:4: (lv_multiplicity_3_0= ruleDefiniteMultiplicity )
            {
            // InternalProblemParser.g:4597:4: (lv_multiplicity_3_0= ruleDefiniteMultiplicity )
            // InternalProblemParser.g:4598:5: lv_multiplicity_3_0= ruleDefiniteMultiplicity
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getTypeScopeAccess().getMultiplicityDefiniteMultiplicityParserRuleCall_2_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_multiplicity_3_0=ruleDefiniteMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getTypeScopeRule());
              					}
              					set(
              						current,
              						"multiplicity",
              						lv_multiplicity_3_0,
              						"tools.refinery.language.Problem.DefiniteMultiplicity");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleTypeScope"


    // $ANTLR start "entryRuleMultiplicity"
    // InternalProblemParser.g:4619:1: entryRuleMultiplicity returns [EObject current=null] : iv_ruleMultiplicity= ruleMultiplicity EOF ;
    public final EObject entryRuleMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMultiplicity = null;


        try {
            // InternalProblemParser.g:4619:53: (iv_ruleMultiplicity= ruleMultiplicity EOF )
            // InternalProblemParser.g:4620:2: iv_ruleMultiplicity= ruleMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleMultiplicity=ruleMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleMultiplicity"


    // $ANTLR start "ruleMultiplicity"
    // InternalProblemParser.g:4626:1: ruleMultiplicity returns [EObject current=null] : (this_UnboundedMultiplicity_0= ruleUnboundedMultiplicity | this_DefiniteMultiplicity_1= ruleDefiniteMultiplicity ) ;
    public final EObject ruleMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject this_UnboundedMultiplicity_0 = null;

        EObject this_DefiniteMultiplicity_1 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4632:2: ( (this_UnboundedMultiplicity_0= ruleUnboundedMultiplicity | this_DefiniteMultiplicity_1= ruleDefiniteMultiplicity ) )
            // InternalProblemParser.g:4633:2: (this_UnboundedMultiplicity_0= ruleUnboundedMultiplicity | this_DefiniteMultiplicity_1= ruleDefiniteMultiplicity )
            {
            // InternalProblemParser.g:4633:2: (this_UnboundedMultiplicity_0= ruleUnboundedMultiplicity | this_DefiniteMultiplicity_1= ruleDefiniteMultiplicity )
            int alt91=2;
            int LA91_0 = input.LA(1);

            if ( (LA91_0==EOF||LA91_0==RightSquareBracket) ) {
                alt91=1;
            }
            else if ( (LA91_0==RULE_INT) ) {
                alt91=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 91, 0, input);

                throw nvae;
            }
            switch (alt91) {
                case 1 :
                    // InternalProblemParser.g:4634:3: this_UnboundedMultiplicity_0= ruleUnboundedMultiplicity
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getMultiplicityAccess().getUnboundedMultiplicityParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_UnboundedMultiplicity_0=ruleUnboundedMultiplicity();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_UnboundedMultiplicity_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4643:3: this_DefiniteMultiplicity_1= ruleDefiniteMultiplicity
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getMultiplicityAccess().getDefiniteMultiplicityParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_DefiniteMultiplicity_1=ruleDefiniteMultiplicity();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_DefiniteMultiplicity_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleMultiplicity"


    // $ANTLR start "entryRuleDefiniteMultiplicity"
    // InternalProblemParser.g:4655:1: entryRuleDefiniteMultiplicity returns [EObject current=null] : iv_ruleDefiniteMultiplicity= ruleDefiniteMultiplicity EOF ;
    public final EObject entryRuleDefiniteMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDefiniteMultiplicity = null;


        try {
            // InternalProblemParser.g:4655:61: (iv_ruleDefiniteMultiplicity= ruleDefiniteMultiplicity EOF )
            // InternalProblemParser.g:4656:2: iv_ruleDefiniteMultiplicity= ruleDefiniteMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getDefiniteMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleDefiniteMultiplicity=ruleDefiniteMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleDefiniteMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleDefiniteMultiplicity"


    // $ANTLR start "ruleDefiniteMultiplicity"
    // InternalProblemParser.g:4662:1: ruleDefiniteMultiplicity returns [EObject current=null] : (this_RangeMultiplicity_0= ruleRangeMultiplicity | this_ExactMultiplicity_1= ruleExactMultiplicity ) ;
    public final EObject ruleDefiniteMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject this_RangeMultiplicity_0 = null;

        EObject this_ExactMultiplicity_1 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4668:2: ( (this_RangeMultiplicity_0= ruleRangeMultiplicity | this_ExactMultiplicity_1= ruleExactMultiplicity ) )
            // InternalProblemParser.g:4669:2: (this_RangeMultiplicity_0= ruleRangeMultiplicity | this_ExactMultiplicity_1= ruleExactMultiplicity )
            {
            // InternalProblemParser.g:4669:2: (this_RangeMultiplicity_0= ruleRangeMultiplicity | this_ExactMultiplicity_1= ruleExactMultiplicity )
            int alt92=2;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==RULE_INT) ) {
                int LA92_1 = input.LA(2);

                if ( (LA92_1==FullStopFullStop) ) {
                    alt92=1;
                }
                else if ( (LA92_1==EOF||LA92_1==Comma||LA92_1==FullStop||LA92_1==RightSquareBracket) ) {
                    alt92=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return current;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 92, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 92, 0, input);

                throw nvae;
            }
            switch (alt92) {
                case 1 :
                    // InternalProblemParser.g:4670:3: this_RangeMultiplicity_0= ruleRangeMultiplicity
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getDefiniteMultiplicityAccess().getRangeMultiplicityParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_RangeMultiplicity_0=ruleRangeMultiplicity();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_RangeMultiplicity_0;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4679:3: this_ExactMultiplicity_1= ruleExactMultiplicity
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getDefiniteMultiplicityAccess().getExactMultiplicityParserRuleCall_1());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_ExactMultiplicity_1=ruleExactMultiplicity();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current = this_ExactMultiplicity_1;
                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleDefiniteMultiplicity"


    // $ANTLR start "entryRuleUnboundedMultiplicity"
    // InternalProblemParser.g:4691:1: entryRuleUnboundedMultiplicity returns [EObject current=null] : iv_ruleUnboundedMultiplicity= ruleUnboundedMultiplicity EOF ;
    public final EObject entryRuleUnboundedMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleUnboundedMultiplicity = null;


        try {
            // InternalProblemParser.g:4691:62: (iv_ruleUnboundedMultiplicity= ruleUnboundedMultiplicity EOF )
            // InternalProblemParser.g:4692:2: iv_ruleUnboundedMultiplicity= ruleUnboundedMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getUnboundedMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleUnboundedMultiplicity=ruleUnboundedMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleUnboundedMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleUnboundedMultiplicity"


    // $ANTLR start "ruleUnboundedMultiplicity"
    // InternalProblemParser.g:4698:1: ruleUnboundedMultiplicity returns [EObject current=null] : () ;
    public final EObject ruleUnboundedMultiplicity() throws RecognitionException {
        EObject current = null;


        	enterRule();

        try {
            // InternalProblemParser.g:4704:2: ( () )
            // InternalProblemParser.g:4705:2: ()
            {
            // InternalProblemParser.g:4705:2: ()
            // InternalProblemParser.g:4706:3: 
            {
            if ( state.backtracking==0 ) {

              			current = forceCreateModelElement(
              				grammarAccess.getUnboundedMultiplicityAccess().getUnboundedMultiplicityAction(),
              				current);
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleUnboundedMultiplicity"


    // $ANTLR start "entryRuleRangeMultiplicity"
    // InternalProblemParser.g:4715:1: entryRuleRangeMultiplicity returns [EObject current=null] : iv_ruleRangeMultiplicity= ruleRangeMultiplicity EOF ;
    public final EObject entryRuleRangeMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRangeMultiplicity = null;


        try {
            // InternalProblemParser.g:4715:58: (iv_ruleRangeMultiplicity= ruleRangeMultiplicity EOF )
            // InternalProblemParser.g:4716:2: iv_ruleRangeMultiplicity= ruleRangeMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getRangeMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleRangeMultiplicity=ruleRangeMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleRangeMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleRangeMultiplicity"


    // $ANTLR start "ruleRangeMultiplicity"
    // InternalProblemParser.g:4722:1: ruleRangeMultiplicity returns [EObject current=null] : ( ( (lv_lowerBound_0_0= RULE_INT ) ) otherlv_1= FullStopFullStop ( (lv_upperBound_2_0= ruleUpperBound ) ) ) ;
    public final EObject ruleRangeMultiplicity() throws RecognitionException {
        EObject current = null;

        Token lv_lowerBound_0_0=null;
        Token otherlv_1=null;
        AntlrDatatypeRuleToken lv_upperBound_2_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4728:2: ( ( ( (lv_lowerBound_0_0= RULE_INT ) ) otherlv_1= FullStopFullStop ( (lv_upperBound_2_0= ruleUpperBound ) ) ) )
            // InternalProblemParser.g:4729:2: ( ( (lv_lowerBound_0_0= RULE_INT ) ) otherlv_1= FullStopFullStop ( (lv_upperBound_2_0= ruleUpperBound ) ) )
            {
            // InternalProblemParser.g:4729:2: ( ( (lv_lowerBound_0_0= RULE_INT ) ) otherlv_1= FullStopFullStop ( (lv_upperBound_2_0= ruleUpperBound ) ) )
            // InternalProblemParser.g:4730:3: ( (lv_lowerBound_0_0= RULE_INT ) ) otherlv_1= FullStopFullStop ( (lv_upperBound_2_0= ruleUpperBound ) )
            {
            // InternalProblemParser.g:4730:3: ( (lv_lowerBound_0_0= RULE_INT ) )
            // InternalProblemParser.g:4731:4: (lv_lowerBound_0_0= RULE_INT )
            {
            // InternalProblemParser.g:4731:4: (lv_lowerBound_0_0= RULE_INT )
            // InternalProblemParser.g:4732:5: lv_lowerBound_0_0= RULE_INT
            {
            lv_lowerBound_0_0=(Token)match(input,RULE_INT,FOLLOW_67); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					newLeafNode(lv_lowerBound_0_0, grammarAccess.getRangeMultiplicityAccess().getLowerBoundINTTerminalRuleCall_0_0());
              				
            }
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElement(grammarAccess.getRangeMultiplicityRule());
              					}
              					setWithLastConsumed(
              						current,
              						"lowerBound",
              						lv_lowerBound_0_0,
              						"org.eclipse.xtext.common.Terminals.INT");
              				
            }

            }


            }

            otherlv_1=(Token)match(input,FullStopFullStop,FOLLOW_68); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(otherlv_1, grammarAccess.getRangeMultiplicityAccess().getFullStopFullStopKeyword_1());
              		
            }
            // InternalProblemParser.g:4752:3: ( (lv_upperBound_2_0= ruleUpperBound ) )
            // InternalProblemParser.g:4753:4: (lv_upperBound_2_0= ruleUpperBound )
            {
            // InternalProblemParser.g:4753:4: (lv_upperBound_2_0= ruleUpperBound )
            // InternalProblemParser.g:4754:5: lv_upperBound_2_0= ruleUpperBound
            {
            if ( state.backtracking==0 ) {

              					newCompositeNode(grammarAccess.getRangeMultiplicityAccess().getUpperBoundUpperBoundParserRuleCall_2_0());
              				
            }
            pushFollow(FOLLOW_2);
            lv_upperBound_2_0=ruleUpperBound();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              					if (current==null) {
              						current = createModelElementForParent(grammarAccess.getRangeMultiplicityRule());
              					}
              					set(
              						current,
              						"upperBound",
              						lv_upperBound_2_0,
              						"tools.refinery.language.Problem.UpperBound");
              					afterParserOrEnumRuleCall();
              				
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleRangeMultiplicity"


    // $ANTLR start "entryRuleExactMultiplicity"
    // InternalProblemParser.g:4775:1: entryRuleExactMultiplicity returns [EObject current=null] : iv_ruleExactMultiplicity= ruleExactMultiplicity EOF ;
    public final EObject entryRuleExactMultiplicity() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExactMultiplicity = null;


        try {
            // InternalProblemParser.g:4775:58: (iv_ruleExactMultiplicity= ruleExactMultiplicity EOF )
            // InternalProblemParser.g:4776:2: iv_ruleExactMultiplicity= ruleExactMultiplicity EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getExactMultiplicityRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleExactMultiplicity=ruleExactMultiplicity();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleExactMultiplicity; 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleExactMultiplicity"


    // $ANTLR start "ruleExactMultiplicity"
    // InternalProblemParser.g:4782:1: ruleExactMultiplicity returns [EObject current=null] : ( (lv_exactValue_0_0= RULE_INT ) ) ;
    public final EObject ruleExactMultiplicity() throws RecognitionException {
        EObject current = null;

        Token lv_exactValue_0_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:4788:2: ( ( (lv_exactValue_0_0= RULE_INT ) ) )
            // InternalProblemParser.g:4789:2: ( (lv_exactValue_0_0= RULE_INT ) )
            {
            // InternalProblemParser.g:4789:2: ( (lv_exactValue_0_0= RULE_INT ) )
            // InternalProblemParser.g:4790:3: (lv_exactValue_0_0= RULE_INT )
            {
            // InternalProblemParser.g:4790:3: (lv_exactValue_0_0= RULE_INT )
            // InternalProblemParser.g:4791:4: lv_exactValue_0_0= RULE_INT
            {
            lv_exactValue_0_0=(Token)match(input,RULE_INT,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              				newLeafNode(lv_exactValue_0_0, grammarAccess.getExactMultiplicityAccess().getExactValueINTTerminalRuleCall_0());
              			
            }
            if ( state.backtracking==0 ) {

              				if (current==null) {
              					current = createModelElement(grammarAccess.getExactMultiplicityRule());
              				}
              				setWithLastConsumed(
              					current,
              					"exactValue",
              					lv_exactValue_0_0,
              					"org.eclipse.xtext.common.Terminals.INT");
              			
            }

            }


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleExactMultiplicity"


    // $ANTLR start "entryRuleUpperBound"
    // InternalProblemParser.g:4810:1: entryRuleUpperBound returns [String current=null] : iv_ruleUpperBound= ruleUpperBound EOF ;
    public final String entryRuleUpperBound() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleUpperBound = null;


        try {
            // InternalProblemParser.g:4810:50: (iv_ruleUpperBound= ruleUpperBound EOF )
            // InternalProblemParser.g:4811:2: iv_ruleUpperBound= ruleUpperBound EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getUpperBoundRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleUpperBound=ruleUpperBound();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleUpperBound.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleUpperBound"


    // $ANTLR start "ruleUpperBound"
    // InternalProblemParser.g:4817:1: ruleUpperBound returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (this_INT_0= RULE_INT | kw= Asterisk ) ;
    public final AntlrDatatypeRuleToken ruleUpperBound() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_INT_0=null;
        Token kw=null;


        	enterRule();

        try {
            // InternalProblemParser.g:4823:2: ( (this_INT_0= RULE_INT | kw= Asterisk ) )
            // InternalProblemParser.g:4824:2: (this_INT_0= RULE_INT | kw= Asterisk )
            {
            // InternalProblemParser.g:4824:2: (this_INT_0= RULE_INT | kw= Asterisk )
            int alt93=2;
            int LA93_0 = input.LA(1);

            if ( (LA93_0==RULE_INT) ) {
                alt93=1;
            }
            else if ( (LA93_0==Asterisk) ) {
                alt93=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 93, 0, input);

                throw nvae;
            }
            switch (alt93) {
                case 1 :
                    // InternalProblemParser.g:4825:3: this_INT_0= RULE_INT
                    {
                    this_INT_0=(Token)match(input,RULE_INT,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(this_INT_0);
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			newLeafNode(this_INT_0, grammarAccess.getUpperBoundAccess().getINTTerminalRuleCall_0());
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4833:3: kw= Asterisk
                    {
                    kw=(Token)match(input,Asterisk,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getUpperBoundAccess().getAsteriskKeyword_1());
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleUpperBound"


    // $ANTLR start "entryRuleQualifiedName"
    // InternalProblemParser.g:4842:1: entryRuleQualifiedName returns [String current=null] : iv_ruleQualifiedName= ruleQualifiedName EOF ;
    public final String entryRuleQualifiedName() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleQualifiedName = null;



        	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens();

        try {
            // InternalProblemParser.g:4844:2: (iv_ruleQualifiedName= ruleQualifiedName EOF )
            // InternalProblemParser.g:4845:2: iv_ruleQualifiedName= ruleQualifiedName EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getQualifiedNameRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleQualifiedName=ruleQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleQualifiedName.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {

            	myHiddenTokenState.restore();

        }
        return current;
    }
    // $ANTLR end "entryRuleQualifiedName"


    // $ANTLR start "ruleQualifiedName"
    // InternalProblemParser.g:4854:1: ruleQualifiedName returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : ( (kw= ColonColon )? this_Identifier_1= ruleIdentifier (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )* ) ;
    public final AntlrDatatypeRuleToken ruleQualifiedName() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token kw=null;
        Token this_QUALIFIED_NAME_SEPARATOR_2=null;
        AntlrDatatypeRuleToken this_Identifier_1 = null;

        AntlrDatatypeRuleToken this_Identifier_3 = null;



        	enterRule();
        	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens();

        try {
            // InternalProblemParser.g:4861:2: ( ( (kw= ColonColon )? this_Identifier_1= ruleIdentifier (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )* ) )
            // InternalProblemParser.g:4862:2: ( (kw= ColonColon )? this_Identifier_1= ruleIdentifier (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )* )
            {
            // InternalProblemParser.g:4862:2: ( (kw= ColonColon )? this_Identifier_1= ruleIdentifier (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )* )
            // InternalProblemParser.g:4863:3: (kw= ColonColon )? this_Identifier_1= ruleIdentifier (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )*
            {
            // InternalProblemParser.g:4863:3: (kw= ColonColon )?
            int alt94=2;
            int LA94_0 = input.LA(1);

            if ( (LA94_0==ColonColon) ) {
                alt94=1;
            }
            switch (alt94) {
                case 1 :
                    // InternalProblemParser.g:4864:4: kw= ColonColon
                    {
                    kw=(Token)match(input,ColonColon,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current.merge(kw);
                      				newLeafNode(kw, grammarAccess.getQualifiedNameAccess().getColonColonKeyword_0());
                      			
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {

              			newCompositeNode(grammarAccess.getQualifiedNameAccess().getIdentifierParserRuleCall_1());
              		
            }
            pushFollow(FOLLOW_69);
            this_Identifier_1=ruleIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current.merge(this_Identifier_1);
              		
            }
            if ( state.backtracking==0 ) {

              			afterParserOrEnumRuleCall();
              		
            }
            // InternalProblemParser.g:4880:3: (this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier )*
            loop95:
            do {
                int alt95=2;
                int LA95_0 = input.LA(1);

                if ( (LA95_0==RULE_QUALIFIED_NAME_SEPARATOR) ) {
                    alt95=1;
                }


                switch (alt95) {
            	case 1 :
            	    // InternalProblemParser.g:4881:4: this_QUALIFIED_NAME_SEPARATOR_2= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_3= ruleIdentifier
            	    {
            	    this_QUALIFIED_NAME_SEPARATOR_2=(Token)match(input,RULE_QUALIFIED_NAME_SEPARATOR,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				current.merge(this_QUALIFIED_NAME_SEPARATOR_2);
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(this_QUALIFIED_NAME_SEPARATOR_2, grammarAccess.getQualifiedNameAccess().getQUALIFIED_NAME_SEPARATORTerminalRuleCall_2_0());
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				newCompositeNode(grammarAccess.getQualifiedNameAccess().getIdentifierParserRuleCall_2_1());
            	      			
            	    }
            	    pushFollow(FOLLOW_69);
            	    this_Identifier_3=ruleIdentifier();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				current.merge(this_Identifier_3);
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				afterParserOrEnumRuleCall();
            	      			
            	    }

            	    }
            	    break;

            	default :
            	    break loop95;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {

            	myHiddenTokenState.restore();

        }
        return current;
    }
    // $ANTLR end "ruleQualifiedName"


    // $ANTLR start "entryRuleNonContainmentQualifiedName"
    // InternalProblemParser.g:4906:1: entryRuleNonContainmentQualifiedName returns [String current=null] : iv_ruleNonContainmentQualifiedName= ruleNonContainmentQualifiedName EOF ;
    public final String entryRuleNonContainmentQualifiedName() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleNonContainmentQualifiedName = null;



        	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens();

        try {
            // InternalProblemParser.g:4908:2: (iv_ruleNonContainmentQualifiedName= ruleNonContainmentQualifiedName EOF )
            // InternalProblemParser.g:4909:2: iv_ruleNonContainmentQualifiedName= ruleNonContainmentQualifiedName EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNonContainmentQualifiedNameRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleNonContainmentQualifiedName=ruleNonContainmentQualifiedName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNonContainmentQualifiedName.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {

            	myHiddenTokenState.restore();

        }
        return current;
    }
    // $ANTLR end "entryRuleNonContainmentQualifiedName"


    // $ANTLR start "ruleNonContainmentQualifiedName"
    // InternalProblemParser.g:4918:1: ruleNonContainmentQualifiedName returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : ( (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) ) (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )* ) ;
    public final AntlrDatatypeRuleToken ruleNonContainmentQualifiedName() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token kw=null;
        Token this_QUALIFIED_NAME_SEPARATOR_3=null;
        AntlrDatatypeRuleToken this_NonContainmentIdentifier_0 = null;

        AntlrDatatypeRuleToken this_Identifier_2 = null;

        AntlrDatatypeRuleToken this_Identifier_4 = null;



        	enterRule();
        	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens();

        try {
            // InternalProblemParser.g:4925:2: ( ( (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) ) (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )* ) )
            // InternalProblemParser.g:4926:2: ( (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) ) (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )* )
            {
            // InternalProblemParser.g:4926:2: ( (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) ) (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )* )
            // InternalProblemParser.g:4927:3: (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) ) (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )*
            {
            // InternalProblemParser.g:4927:3: (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | (kw= ColonColon this_Identifier_2= ruleIdentifier ) )
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( ((LA96_0>=Concretization && LA96_0<=Aggregator)||LA96_0==Primitive||(LA96_0>=Datatype && LA96_0<=Decision)||LA96_0==Problem||LA96_0==Assert||LA96_0==Module||LA96_0==Shadow||LA96_0==Multi||LA96_0==Atom||LA96_0==As||LA96_0==RULE_ID||LA96_0==RULE_QUOTED_ID) ) {
                alt96=1;
            }
            else if ( (LA96_0==ColonColon) ) {
                alt96=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 96, 0, input);

                throw nvae;
            }
            switch (alt96) {
                case 1 :
                    // InternalProblemParser.g:4928:4: this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      				newCompositeNode(grammarAccess.getNonContainmentQualifiedNameAccess().getNonContainmentIdentifierParserRuleCall_0_0());
                      			
                    }
                    pushFollow(FOLLOW_69);
                    this_NonContainmentIdentifier_0=ruleNonContainmentIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current.merge(this_NonContainmentIdentifier_0);
                      			
                    }
                    if ( state.backtracking==0 ) {

                      				afterParserOrEnumRuleCall();
                      			
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:4939:4: (kw= ColonColon this_Identifier_2= ruleIdentifier )
                    {
                    // InternalProblemParser.g:4939:4: (kw= ColonColon this_Identifier_2= ruleIdentifier )
                    // InternalProblemParser.g:4940:5: kw= ColonColon this_Identifier_2= ruleIdentifier
                    {
                    kw=(Token)match(input,ColonColon,FOLLOW_8); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					current.merge(kw);
                      					newLeafNode(kw, grammarAccess.getNonContainmentQualifiedNameAccess().getColonColonKeyword_0_1_0());
                      				
                    }
                    if ( state.backtracking==0 ) {

                      					newCompositeNode(grammarAccess.getNonContainmentQualifiedNameAccess().getIdentifierParserRuleCall_0_1_1());
                      				
                    }
                    pushFollow(FOLLOW_69);
                    this_Identifier_2=ruleIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      					current.merge(this_Identifier_2);
                      				
                    }
                    if ( state.backtracking==0 ) {

                      					afterParserOrEnumRuleCall();
                      				
                    }

                    }


                    }
                    break;

            }

            // InternalProblemParser.g:4957:3: (this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier )*
            loop97:
            do {
                int alt97=2;
                int LA97_0 = input.LA(1);

                if ( (LA97_0==RULE_QUALIFIED_NAME_SEPARATOR) ) {
                    alt97=1;
                }


                switch (alt97) {
            	case 1 :
            	    // InternalProblemParser.g:4958:4: this_QUALIFIED_NAME_SEPARATOR_3= RULE_QUALIFIED_NAME_SEPARATOR this_Identifier_4= ruleIdentifier
            	    {
            	    this_QUALIFIED_NAME_SEPARATOR_3=(Token)match(input,RULE_QUALIFIED_NAME_SEPARATOR,FOLLOW_8); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				current.merge(this_QUALIFIED_NAME_SEPARATOR_3);
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				newLeafNode(this_QUALIFIED_NAME_SEPARATOR_3, grammarAccess.getNonContainmentQualifiedNameAccess().getQUALIFIED_NAME_SEPARATORTerminalRuleCall_1_0());
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				newCompositeNode(grammarAccess.getNonContainmentQualifiedNameAccess().getIdentifierParserRuleCall_1_1());
            	      			
            	    }
            	    pushFollow(FOLLOW_69);
            	    this_Identifier_4=ruleIdentifier();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      				current.merge(this_Identifier_4);
            	      			
            	    }
            	    if ( state.backtracking==0 ) {

            	      				afterParserOrEnumRuleCall();
            	      			
            	    }

            	    }
            	    break;

            	default :
            	    break loop97;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {

            	myHiddenTokenState.restore();

        }
        return current;
    }
    // $ANTLR end "ruleNonContainmentQualifiedName"


    // $ANTLR start "entryRuleIdentifier"
    // InternalProblemParser.g:4983:1: entryRuleIdentifier returns [String current=null] : iv_ruleIdentifier= ruleIdentifier EOF ;
    public final String entryRuleIdentifier() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleIdentifier = null;


        try {
            // InternalProblemParser.g:4983:50: (iv_ruleIdentifier= ruleIdentifier EOF )
            // InternalProblemParser.g:4984:2: iv_ruleIdentifier= ruleIdentifier EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIdentifierRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleIdentifier=ruleIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleIdentifier.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleIdentifier"


    // $ANTLR start "ruleIdentifier"
    // InternalProblemParser.g:4990:1: ruleIdentifier returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | kw= Contains | kw= Container | kw= Opposite | kw= Subsets ) ;
    public final AntlrDatatypeRuleToken ruleIdentifier() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token kw=null;
        AntlrDatatypeRuleToken this_NonContainmentIdentifier_0 = null;



        	enterRule();

        try {
            // InternalProblemParser.g:4996:2: ( (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | kw= Contains | kw= Container | kw= Opposite | kw= Subsets ) )
            // InternalProblemParser.g:4997:2: (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | kw= Contains | kw= Container | kw= Opposite | kw= Subsets )
            {
            // InternalProblemParser.g:4997:2: (this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier | kw= Contains | kw= Container | kw= Opposite | kw= Subsets )
            int alt98=5;
            switch ( input.LA(1) ) {
            case Concretization:
            case Propagation:
            case Aggregator:
            case Primitive:
            case Datatype:
            case Decision:
            case Problem:
            case Assert:
            case Module:
            case Shadow:
            case Multi:
            case Atom:
            case As:
            case RULE_ID:
            case RULE_QUOTED_ID:
                {
                alt98=1;
                }
                break;
            case Contains:
                {
                alt98=2;
                }
                break;
            case Container:
                {
                alt98=3;
                }
                break;
            case Opposite:
                {
                alt98=4;
                }
                break;
            case Subsets:
                {
                alt98=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 98, 0, input);

                throw nvae;
            }

            switch (alt98) {
                case 1 :
                    // InternalProblemParser.g:4998:3: this_NonContainmentIdentifier_0= ruleNonContainmentIdentifier
                    {
                    if ( state.backtracking==0 ) {

                      			newCompositeNode(grammarAccess.getIdentifierAccess().getNonContainmentIdentifierParserRuleCall_0());
                      		
                    }
                    pushFollow(FOLLOW_2);
                    this_NonContainmentIdentifier_0=ruleNonContainmentIdentifier();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(this_NonContainmentIdentifier_0);
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			afterParserOrEnumRuleCall();
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5009:3: kw= Contains
                    {
                    kw=(Token)match(input,Contains,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getIdentifierAccess().getContainsKeyword_1());
                      		
                    }

                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5015:3: kw= Container
                    {
                    kw=(Token)match(input,Container,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getIdentifierAccess().getContainerKeyword_2());
                      		
                    }

                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:5021:3: kw= Opposite
                    {
                    kw=(Token)match(input,Opposite,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getIdentifierAccess().getOppositeKeyword_3());
                      		
                    }

                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:5027:3: kw= Subsets
                    {
                    kw=(Token)match(input,Subsets,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getIdentifierAccess().getSubsetsKeyword_4());
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleIdentifier"


    // $ANTLR start "entryRuleNonContainmentIdentifier"
    // InternalProblemParser.g:5036:1: entryRuleNonContainmentIdentifier returns [String current=null] : iv_ruleNonContainmentIdentifier= ruleNonContainmentIdentifier EOF ;
    public final String entryRuleNonContainmentIdentifier() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleNonContainmentIdentifier = null;


        try {
            // InternalProblemParser.g:5036:64: (iv_ruleNonContainmentIdentifier= ruleNonContainmentIdentifier EOF )
            // InternalProblemParser.g:5037:2: iv_ruleNonContainmentIdentifier= ruleNonContainmentIdentifier EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNonContainmentIdentifierRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleNonContainmentIdentifier=ruleNonContainmentIdentifier();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNonContainmentIdentifier.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleNonContainmentIdentifier"


    // $ANTLR start "ruleNonContainmentIdentifier"
    // InternalProblemParser.g:5043:1: ruleNonContainmentIdentifier returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (this_ID_0= RULE_ID | this_QUOTED_ID_1= RULE_QUOTED_ID | kw= As | kw= Atom | kw= Multi | kw= Problem | kw= Module | kw= Datatype | kw= Aggregator | kw= Primitive | kw= Decision | kw= Propagation | kw= Concretization | kw= Shadow | kw= Assert ) ;
    public final AntlrDatatypeRuleToken ruleNonContainmentIdentifier() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_ID_0=null;
        Token this_QUOTED_ID_1=null;
        Token kw=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5049:2: ( (this_ID_0= RULE_ID | this_QUOTED_ID_1= RULE_QUOTED_ID | kw= As | kw= Atom | kw= Multi | kw= Problem | kw= Module | kw= Datatype | kw= Aggregator | kw= Primitive | kw= Decision | kw= Propagation | kw= Concretization | kw= Shadow | kw= Assert ) )
            // InternalProblemParser.g:5050:2: (this_ID_0= RULE_ID | this_QUOTED_ID_1= RULE_QUOTED_ID | kw= As | kw= Atom | kw= Multi | kw= Problem | kw= Module | kw= Datatype | kw= Aggregator | kw= Primitive | kw= Decision | kw= Propagation | kw= Concretization | kw= Shadow | kw= Assert )
            {
            // InternalProblemParser.g:5050:2: (this_ID_0= RULE_ID | this_QUOTED_ID_1= RULE_QUOTED_ID | kw= As | kw= Atom | kw= Multi | kw= Problem | kw= Module | kw= Datatype | kw= Aggregator | kw= Primitive | kw= Decision | kw= Propagation | kw= Concretization | kw= Shadow | kw= Assert )
            int alt99=15;
            switch ( input.LA(1) ) {
            case RULE_ID:
                {
                alt99=1;
                }
                break;
            case RULE_QUOTED_ID:
                {
                alt99=2;
                }
                break;
            case As:
                {
                alt99=3;
                }
                break;
            case Atom:
                {
                alt99=4;
                }
                break;
            case Multi:
                {
                alt99=5;
                }
                break;
            case Problem:
                {
                alt99=6;
                }
                break;
            case Module:
                {
                alt99=7;
                }
                break;
            case Datatype:
                {
                alt99=8;
                }
                break;
            case Aggregator:
                {
                alt99=9;
                }
                break;
            case Primitive:
                {
                alt99=10;
                }
                break;
            case Decision:
                {
                alt99=11;
                }
                break;
            case Propagation:
                {
                alt99=12;
                }
                break;
            case Concretization:
                {
                alt99=13;
                }
                break;
            case Shadow:
                {
                alt99=14;
                }
                break;
            case Assert:
                {
                alt99=15;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 99, 0, input);

                throw nvae;
            }

            switch (alt99) {
                case 1 :
                    // InternalProblemParser.g:5051:3: this_ID_0= RULE_ID
                    {
                    this_ID_0=(Token)match(input,RULE_ID,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(this_ID_0);
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			newLeafNode(this_ID_0, grammarAccess.getNonContainmentIdentifierAccess().getIDTerminalRuleCall_0());
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5059:3: this_QUOTED_ID_1= RULE_QUOTED_ID
                    {
                    this_QUOTED_ID_1=(Token)match(input,RULE_QUOTED_ID,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(this_QUOTED_ID_1);
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			newLeafNode(this_QUOTED_ID_1, grammarAccess.getNonContainmentIdentifierAccess().getQUOTED_IDTerminalRuleCall_1());
                      		
                    }

                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5067:3: kw= As
                    {
                    kw=(Token)match(input,As,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getAsKeyword_2());
                      		
                    }

                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:5073:3: kw= Atom
                    {
                    kw=(Token)match(input,Atom,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getAtomKeyword_3());
                      		
                    }

                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:5079:3: kw= Multi
                    {
                    kw=(Token)match(input,Multi,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getMultiKeyword_4());
                      		
                    }

                    }
                    break;
                case 6 :
                    // InternalProblemParser.g:5085:3: kw= Problem
                    {
                    kw=(Token)match(input,Problem,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getProblemKeyword_5());
                      		
                    }

                    }
                    break;
                case 7 :
                    // InternalProblemParser.g:5091:3: kw= Module
                    {
                    kw=(Token)match(input,Module,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getModuleKeyword_6());
                      		
                    }

                    }
                    break;
                case 8 :
                    // InternalProblemParser.g:5097:3: kw= Datatype
                    {
                    kw=(Token)match(input,Datatype,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getDatatypeKeyword_7());
                      		
                    }

                    }
                    break;
                case 9 :
                    // InternalProblemParser.g:5103:3: kw= Aggregator
                    {
                    kw=(Token)match(input,Aggregator,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getAggregatorKeyword_8());
                      		
                    }

                    }
                    break;
                case 10 :
                    // InternalProblemParser.g:5109:3: kw= Primitive
                    {
                    kw=(Token)match(input,Primitive,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getPrimitiveKeyword_9());
                      		
                    }

                    }
                    break;
                case 11 :
                    // InternalProblemParser.g:5115:3: kw= Decision
                    {
                    kw=(Token)match(input,Decision,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getDecisionKeyword_10());
                      		
                    }

                    }
                    break;
                case 12 :
                    // InternalProblemParser.g:5121:3: kw= Propagation
                    {
                    kw=(Token)match(input,Propagation,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getPropagationKeyword_11());
                      		
                    }

                    }
                    break;
                case 13 :
                    // InternalProblemParser.g:5127:3: kw= Concretization
                    {
                    kw=(Token)match(input,Concretization,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getConcretizationKeyword_12());
                      		
                    }

                    }
                    break;
                case 14 :
                    // InternalProblemParser.g:5133:3: kw= Shadow
                    {
                    kw=(Token)match(input,Shadow,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getShadowKeyword_13());
                      		
                    }

                    }
                    break;
                case 15 :
                    // InternalProblemParser.g:5139:3: kw= Assert
                    {
                    kw=(Token)match(input,Assert,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(kw);
                      			newLeafNode(kw, grammarAccess.getNonContainmentIdentifierAccess().getAssertKeyword_14());
                      		
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleNonContainmentIdentifier"


    // $ANTLR start "entryRuleInteger"
    // InternalProblemParser.g:5148:1: entryRuleInteger returns [String current=null] : iv_ruleInteger= ruleInteger EOF ;
    public final String entryRuleInteger() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleInteger = null;


        try {
            // InternalProblemParser.g:5148:47: (iv_ruleInteger= ruleInteger EOF )
            // InternalProblemParser.g:5149:2: iv_ruleInteger= ruleInteger EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIntegerRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleInteger=ruleInteger();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleInteger.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleInteger"


    // $ANTLR start "ruleInteger"
    // InternalProblemParser.g:5155:1: ruleInteger returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : this_INT_0= RULE_INT ;
    public final AntlrDatatypeRuleToken ruleInteger() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_INT_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5161:2: (this_INT_0= RULE_INT )
            // InternalProblemParser.g:5162:2: this_INT_0= RULE_INT
            {
            this_INT_0=(Token)match(input,RULE_INT,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current.merge(this_INT_0);
              	
            }
            if ( state.backtracking==0 ) {

              		newLeafNode(this_INT_0, grammarAccess.getIntegerAccess().getINTTerminalRuleCall());
              	
            }

            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleInteger"


    // $ANTLR start "entryRuleReal"
    // InternalProblemParser.g:5172:1: entryRuleReal returns [String current=null] : iv_ruleReal= ruleReal EOF ;
    public final String entryRuleReal() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleReal = null;


        try {
            // InternalProblemParser.g:5172:44: (iv_ruleReal= ruleReal EOF )
            // InternalProblemParser.g:5173:2: iv_ruleReal= ruleReal EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getRealRule()); 
            }
            pushFollow(FOLLOW_1);
            iv_ruleReal=ruleReal();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleReal.getText(); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return current;

            }

        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "entryRuleReal"


    // $ANTLR start "ruleReal"
    // InternalProblemParser.g:5179:1: ruleReal returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (this_EXPONENTIAL_0= RULE_EXPONENTIAL | (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) ) ) ;
    public final AntlrDatatypeRuleToken ruleReal() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_EXPONENTIAL_0=null;
        Token this_INT_1=null;
        Token kw=null;
        Token this_INT_3=null;
        Token this_EXPONENTIAL_4=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5185:2: ( (this_EXPONENTIAL_0= RULE_EXPONENTIAL | (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) ) ) )
            // InternalProblemParser.g:5186:2: (this_EXPONENTIAL_0= RULE_EXPONENTIAL | (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) ) )
            {
            // InternalProblemParser.g:5186:2: (this_EXPONENTIAL_0= RULE_EXPONENTIAL | (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) ) )
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==RULE_EXPONENTIAL) ) {
                alt101=1;
            }
            else if ( (LA101_0==RULE_INT) ) {
                alt101=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 101, 0, input);

                throw nvae;
            }
            switch (alt101) {
                case 1 :
                    // InternalProblemParser.g:5187:3: this_EXPONENTIAL_0= RULE_EXPONENTIAL
                    {
                    this_EXPONENTIAL_0=(Token)match(input,RULE_EXPONENTIAL,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			current.merge(this_EXPONENTIAL_0);
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			newLeafNode(this_EXPONENTIAL_0, grammarAccess.getRealAccess().getEXPONENTIALTerminalRuleCall_0());
                      		
                    }

                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5195:3: (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) )
                    {
                    // InternalProblemParser.g:5195:3: (this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL ) )
                    // InternalProblemParser.g:5196:4: this_INT_1= RULE_INT kw= FullStop (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL )
                    {
                    this_INT_1=(Token)match(input,RULE_INT,FOLLOW_4); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current.merge(this_INT_1);
                      			
                    }
                    if ( state.backtracking==0 ) {

                      				newLeafNode(this_INT_1, grammarAccess.getRealAccess().getINTTerminalRuleCall_1_0());
                      			
                    }
                    kw=(Token)match(input,FullStop,FOLLOW_70); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current.merge(kw);
                      				newLeafNode(kw, grammarAccess.getRealAccess().getFullStopKeyword_1_1());
                      			
                    }
                    // InternalProblemParser.g:5208:4: (this_INT_3= RULE_INT | this_EXPONENTIAL_4= RULE_EXPONENTIAL )
                    int alt100=2;
                    int LA100_0 = input.LA(1);

                    if ( (LA100_0==RULE_INT) ) {
                        alt100=1;
                    }
                    else if ( (LA100_0==RULE_EXPONENTIAL) ) {
                        alt100=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 100, 0, input);

                        throw nvae;
                    }
                    switch (alt100) {
                        case 1 :
                            // InternalProblemParser.g:5209:5: this_INT_3= RULE_INT
                            {
                            this_INT_3=(Token)match(input,RULE_INT,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              					current.merge(this_INT_3);
                              				
                            }
                            if ( state.backtracking==0 ) {

                              					newLeafNode(this_INT_3, grammarAccess.getRealAccess().getINTTerminalRuleCall_1_2_0());
                              				
                            }

                            }
                            break;
                        case 2 :
                            // InternalProblemParser.g:5217:5: this_EXPONENTIAL_4= RULE_EXPONENTIAL
                            {
                            this_EXPONENTIAL_4=(Token)match(input,RULE_EXPONENTIAL,FOLLOW_2); if (state.failed) return current;
                            if ( state.backtracking==0 ) {

                              					current.merge(this_EXPONENTIAL_4);
                              				
                            }
                            if ( state.backtracking==0 ) {

                              					newLeafNode(this_EXPONENTIAL_4, grammarAccess.getRealAccess().getEXPONENTIALTerminalRuleCall_1_2_1());
                              				
                            }

                            }
                            break;

                    }


                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleReal"


    // $ANTLR start "ruleModuleKind"
    // InternalProblemParser.g:5230:1: ruleModuleKind returns [Enumerator current=null] : ( (enumLiteral_0= Problem ) | (enumLiteral_1= Module ) ) ;
    public final Enumerator ruleModuleKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5236:2: ( ( (enumLiteral_0= Problem ) | (enumLiteral_1= Module ) ) )
            // InternalProblemParser.g:5237:2: ( (enumLiteral_0= Problem ) | (enumLiteral_1= Module ) )
            {
            // InternalProblemParser.g:5237:2: ( (enumLiteral_0= Problem ) | (enumLiteral_1= Module ) )
            int alt102=2;
            int LA102_0 = input.LA(1);

            if ( (LA102_0==Problem) ) {
                alt102=1;
            }
            else if ( (LA102_0==Module) ) {
                alt102=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 102, 0, input);

                throw nvae;
            }
            switch (alt102) {
                case 1 :
                    // InternalProblemParser.g:5238:3: (enumLiteral_0= Problem )
                    {
                    // InternalProblemParser.g:5238:3: (enumLiteral_0= Problem )
                    // InternalProblemParser.g:5239:4: enumLiteral_0= Problem
                    {
                    enumLiteral_0=(Token)match(input,Problem,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getModuleKindAccess().getPROBLEMEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getModuleKindAccess().getPROBLEMEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5246:3: (enumLiteral_1= Module )
                    {
                    // InternalProblemParser.g:5246:3: (enumLiteral_1= Module )
                    // InternalProblemParser.g:5247:4: enumLiteral_1= Module
                    {
                    enumLiteral_1=(Token)match(input,Module,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getModuleKindAccess().getMODULEEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getModuleKindAccess().getMODULEEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleModuleKind"


    // $ANTLR start "ruleReferenceKind"
    // InternalProblemParser.g:5257:1: ruleReferenceKind returns [Enumerator current=null] : ( (enumLiteral_0= Refers ) | (enumLiteral_1= Contains ) | (enumLiteral_2= Container ) ) ;
    public final Enumerator ruleReferenceKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5263:2: ( ( (enumLiteral_0= Refers ) | (enumLiteral_1= Contains ) | (enumLiteral_2= Container ) ) )
            // InternalProblemParser.g:5264:2: ( (enumLiteral_0= Refers ) | (enumLiteral_1= Contains ) | (enumLiteral_2= Container ) )
            {
            // InternalProblemParser.g:5264:2: ( (enumLiteral_0= Refers ) | (enumLiteral_1= Contains ) | (enumLiteral_2= Container ) )
            int alt103=3;
            switch ( input.LA(1) ) {
            case Refers:
                {
                alt103=1;
                }
                break;
            case Contains:
                {
                alt103=2;
                }
                break;
            case Container:
                {
                alt103=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 103, 0, input);

                throw nvae;
            }

            switch (alt103) {
                case 1 :
                    // InternalProblemParser.g:5265:3: (enumLiteral_0= Refers )
                    {
                    // InternalProblemParser.g:5265:3: (enumLiteral_0= Refers )
                    // InternalProblemParser.g:5266:4: enumLiteral_0= Refers
                    {
                    enumLiteral_0=(Token)match(input,Refers,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getReferenceKindAccess().getREFERENCEEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getReferenceKindAccess().getREFERENCEEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5273:3: (enumLiteral_1= Contains )
                    {
                    // InternalProblemParser.g:5273:3: (enumLiteral_1= Contains )
                    // InternalProblemParser.g:5274:4: enumLiteral_1= Contains
                    {
                    enumLiteral_1=(Token)match(input,Contains,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getReferenceKindAccess().getCONTAINMENTEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getReferenceKindAccess().getCONTAINMENTEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5281:3: (enumLiteral_2= Container )
                    {
                    // InternalProblemParser.g:5281:3: (enumLiteral_2= Container )
                    // InternalProblemParser.g:5282:4: enumLiteral_2= Container
                    {
                    enumLiteral_2=(Token)match(input,Container,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getReferenceKindAccess().getCONTAINEREnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getReferenceKindAccess().getCONTAINEREnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleReferenceKind"


    // $ANTLR start "ruleErrorPredicateKind"
    // InternalProblemParser.g:5292:1: ruleErrorPredicateKind returns [Enumerator current=null] : (enumLiteral_0= Error ) ;
    public final Enumerator ruleErrorPredicateKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5298:2: ( (enumLiteral_0= Error ) )
            // InternalProblemParser.g:5299:2: (enumLiteral_0= Error )
            {
            // InternalProblemParser.g:5299:2: (enumLiteral_0= Error )
            // InternalProblemParser.g:5300:3: enumLiteral_0= Error
            {
            enumLiteral_0=(Token)match(input,Error,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = grammarAccess.getErrorPredicateKindAccess().getERROREnumLiteralDeclaration().getEnumLiteral().getInstance();
              			newLeafNode(enumLiteral_0, grammarAccess.getErrorPredicateKindAccess().getERROREnumLiteralDeclaration());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleErrorPredicateKind"


    // $ANTLR start "rulePredicateKind"
    // InternalProblemParser.g:5309:1: rulePredicateKind returns [Enumerator current=null] : ( (enumLiteral_0= Error ) | (enumLiteral_1= Shadow ) ) ;
    public final Enumerator rulePredicateKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5315:2: ( ( (enumLiteral_0= Error ) | (enumLiteral_1= Shadow ) ) )
            // InternalProblemParser.g:5316:2: ( (enumLiteral_0= Error ) | (enumLiteral_1= Shadow ) )
            {
            // InternalProblemParser.g:5316:2: ( (enumLiteral_0= Error ) | (enumLiteral_1= Shadow ) )
            int alt104=2;
            int LA104_0 = input.LA(1);

            if ( (LA104_0==Error) ) {
                alt104=1;
            }
            else if ( (LA104_0==Shadow) ) {
                alt104=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 104, 0, input);

                throw nvae;
            }
            switch (alt104) {
                case 1 :
                    // InternalProblemParser.g:5317:3: (enumLiteral_0= Error )
                    {
                    // InternalProblemParser.g:5317:3: (enumLiteral_0= Error )
                    // InternalProblemParser.g:5318:4: enumLiteral_0= Error
                    {
                    enumLiteral_0=(Token)match(input,Error,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getPredicateKindAccess().getERROREnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getPredicateKindAccess().getERROREnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5325:3: (enumLiteral_1= Shadow )
                    {
                    // InternalProblemParser.g:5325:3: (enumLiteral_1= Shadow )
                    // InternalProblemParser.g:5326:4: enumLiteral_1= Shadow
                    {
                    enumLiteral_1=(Token)match(input,Shadow,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getPredicateKindAccess().getSHADOWEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getPredicateKindAccess().getSHADOWEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "rulePredicateKind"


    // $ANTLR start "ruleRuleKind"
    // InternalProblemParser.g:5336:1: ruleRuleKind returns [Enumerator current=null] : ( (enumLiteral_0= Decision ) | (enumLiteral_1= Propagation ) | (enumLiteral_2= Concretization ) ) ;
    public final Enumerator ruleRuleKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5342:2: ( ( (enumLiteral_0= Decision ) | (enumLiteral_1= Propagation ) | (enumLiteral_2= Concretization ) ) )
            // InternalProblemParser.g:5343:2: ( (enumLiteral_0= Decision ) | (enumLiteral_1= Propagation ) | (enumLiteral_2= Concretization ) )
            {
            // InternalProblemParser.g:5343:2: ( (enumLiteral_0= Decision ) | (enumLiteral_1= Propagation ) | (enumLiteral_2= Concretization ) )
            int alt105=3;
            switch ( input.LA(1) ) {
            case Decision:
                {
                alt105=1;
                }
                break;
            case Propagation:
                {
                alt105=2;
                }
                break;
            case Concretization:
                {
                alt105=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 105, 0, input);

                throw nvae;
            }

            switch (alt105) {
                case 1 :
                    // InternalProblemParser.g:5344:3: (enumLiteral_0= Decision )
                    {
                    // InternalProblemParser.g:5344:3: (enumLiteral_0= Decision )
                    // InternalProblemParser.g:5345:4: enumLiteral_0= Decision
                    {
                    enumLiteral_0=(Token)match(input,Decision,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getRuleKindAccess().getDECISIONEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getRuleKindAccess().getDECISIONEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5352:3: (enumLiteral_1= Propagation )
                    {
                    // InternalProblemParser.g:5352:3: (enumLiteral_1= Propagation )
                    // InternalProblemParser.g:5353:4: enumLiteral_1= Propagation
                    {
                    enumLiteral_1=(Token)match(input,Propagation,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getRuleKindAccess().getPROPAGATIONEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getRuleKindAccess().getPROPAGATIONEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5360:3: (enumLiteral_2= Concretization )
                    {
                    // InternalProblemParser.g:5360:3: (enumLiteral_2= Concretization )
                    // InternalProblemParser.g:5361:4: enumLiteral_2= Concretization
                    {
                    enumLiteral_2=(Token)match(input,Concretization,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getRuleKindAccess().getCONCRETIZATIONEnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getRuleKindAccess().getCONCRETIZATIONEnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleRuleKind"


    // $ANTLR start "ruleParameterKind"
    // InternalProblemParser.g:5371:1: ruleParameterKind returns [Enumerator current=null] : (enumLiteral_0= Pred ) ;
    public final Enumerator ruleParameterKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5377:2: ( (enumLiteral_0= Pred ) )
            // InternalProblemParser.g:5378:2: (enumLiteral_0= Pred )
            {
            // InternalProblemParser.g:5378:2: (enumLiteral_0= Pred )
            // InternalProblemParser.g:5379:3: enumLiteral_0= Pred
            {
            enumLiteral_0=(Token)match(input,Pred,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = grammarAccess.getParameterKindAccess().getPREDEnumLiteralDeclaration().getEnumLiteral().getInstance();
              			newLeafNode(enumLiteral_0, grammarAccess.getParameterKindAccess().getPREDEnumLiteralDeclaration());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleParameterKind"


    // $ANTLR start "ruleBooleanBinaryOp"
    // InternalProblemParser.g:5388:1: ruleBooleanBinaryOp returns [Enumerator current=null] : ( (enumLiteral_0= AmpersandAmpersand ) | (enumLiteral_1= VerticalLineVerticalLine ) | (enumLiteral_2= CircumflexAccentCircumflexAccent ) ) ;
    public final Enumerator ruleBooleanBinaryOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5394:2: ( ( (enumLiteral_0= AmpersandAmpersand ) | (enumLiteral_1= VerticalLineVerticalLine ) | (enumLiteral_2= CircumflexAccentCircumflexAccent ) ) )
            // InternalProblemParser.g:5395:2: ( (enumLiteral_0= AmpersandAmpersand ) | (enumLiteral_1= VerticalLineVerticalLine ) | (enumLiteral_2= CircumflexAccentCircumflexAccent ) )
            {
            // InternalProblemParser.g:5395:2: ( (enumLiteral_0= AmpersandAmpersand ) | (enumLiteral_1= VerticalLineVerticalLine ) | (enumLiteral_2= CircumflexAccentCircumflexAccent ) )
            int alt106=3;
            switch ( input.LA(1) ) {
            case AmpersandAmpersand:
                {
                alt106=1;
                }
                break;
            case VerticalLineVerticalLine:
                {
                alt106=2;
                }
                break;
            case CircumflexAccentCircumflexAccent:
                {
                alt106=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 106, 0, input);

                throw nvae;
            }

            switch (alt106) {
                case 1 :
                    // InternalProblemParser.g:5396:3: (enumLiteral_0= AmpersandAmpersand )
                    {
                    // InternalProblemParser.g:5396:3: (enumLiteral_0= AmpersandAmpersand )
                    // InternalProblemParser.g:5397:4: enumLiteral_0= AmpersandAmpersand
                    {
                    enumLiteral_0=(Token)match(input,AmpersandAmpersand,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getBooleanBinaryOpAccess().getANDEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getBooleanBinaryOpAccess().getANDEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5404:3: (enumLiteral_1= VerticalLineVerticalLine )
                    {
                    // InternalProblemParser.g:5404:3: (enumLiteral_1= VerticalLineVerticalLine )
                    // InternalProblemParser.g:5405:4: enumLiteral_1= VerticalLineVerticalLine
                    {
                    enumLiteral_1=(Token)match(input,VerticalLineVerticalLine,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getBooleanBinaryOpAccess().getOREnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getBooleanBinaryOpAccess().getOREnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5412:3: (enumLiteral_2= CircumflexAccentCircumflexAccent )
                    {
                    // InternalProblemParser.g:5412:3: (enumLiteral_2= CircumflexAccentCircumflexAccent )
                    // InternalProblemParser.g:5413:4: enumLiteral_2= CircumflexAccentCircumflexAccent
                    {
                    enumLiteral_2=(Token)match(input,CircumflexAccentCircumflexAccent,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getBooleanBinaryOpAccess().getXOREnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getBooleanBinaryOpAccess().getXOREnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleBooleanBinaryOp"


    // $ANTLR start "ruleComparisonOp"
    // InternalProblemParser.g:5423:1: ruleComparisonOp returns [Enumerator current=null] : ( (enumLiteral_0= LessThanSign ) | (enumLiteral_1= LessThanSignEqualsSign ) | (enumLiteral_2= GreaterThanSign ) | (enumLiteral_3= GreaterThanSignEqualsSign ) | (enumLiteral_4= EqualsSignEqualsSign ) | (enumLiteral_5= ExclamationMarkEqualsSign ) ) ;
    public final Enumerator ruleComparisonOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;
        Token enumLiteral_3=null;
        Token enumLiteral_4=null;
        Token enumLiteral_5=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5429:2: ( ( (enumLiteral_0= LessThanSign ) | (enumLiteral_1= LessThanSignEqualsSign ) | (enumLiteral_2= GreaterThanSign ) | (enumLiteral_3= GreaterThanSignEqualsSign ) | (enumLiteral_4= EqualsSignEqualsSign ) | (enumLiteral_5= ExclamationMarkEqualsSign ) ) )
            // InternalProblemParser.g:5430:2: ( (enumLiteral_0= LessThanSign ) | (enumLiteral_1= LessThanSignEqualsSign ) | (enumLiteral_2= GreaterThanSign ) | (enumLiteral_3= GreaterThanSignEqualsSign ) | (enumLiteral_4= EqualsSignEqualsSign ) | (enumLiteral_5= ExclamationMarkEqualsSign ) )
            {
            // InternalProblemParser.g:5430:2: ( (enumLiteral_0= LessThanSign ) | (enumLiteral_1= LessThanSignEqualsSign ) | (enumLiteral_2= GreaterThanSign ) | (enumLiteral_3= GreaterThanSignEqualsSign ) | (enumLiteral_4= EqualsSignEqualsSign ) | (enumLiteral_5= ExclamationMarkEqualsSign ) )
            int alt107=6;
            switch ( input.LA(1) ) {
            case LessThanSign:
                {
                alt107=1;
                }
                break;
            case LessThanSignEqualsSign:
                {
                alt107=2;
                }
                break;
            case GreaterThanSign:
                {
                alt107=3;
                }
                break;
            case GreaterThanSignEqualsSign:
                {
                alt107=4;
                }
                break;
            case EqualsSignEqualsSign:
                {
                alt107=5;
                }
                break;
            case ExclamationMarkEqualsSign:
                {
                alt107=6;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 107, 0, input);

                throw nvae;
            }

            switch (alt107) {
                case 1 :
                    // InternalProblemParser.g:5431:3: (enumLiteral_0= LessThanSign )
                    {
                    // InternalProblemParser.g:5431:3: (enumLiteral_0= LessThanSign )
                    // InternalProblemParser.g:5432:4: enumLiteral_0= LessThanSign
                    {
                    enumLiteral_0=(Token)match(input,LessThanSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getLESSEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getComparisonOpAccess().getLESSEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5439:3: (enumLiteral_1= LessThanSignEqualsSign )
                    {
                    // InternalProblemParser.g:5439:3: (enumLiteral_1= LessThanSignEqualsSign )
                    // InternalProblemParser.g:5440:4: enumLiteral_1= LessThanSignEqualsSign
                    {
                    enumLiteral_1=(Token)match(input,LessThanSignEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getLESS_EQEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getComparisonOpAccess().getLESS_EQEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5447:3: (enumLiteral_2= GreaterThanSign )
                    {
                    // InternalProblemParser.g:5447:3: (enumLiteral_2= GreaterThanSign )
                    // InternalProblemParser.g:5448:4: enumLiteral_2= GreaterThanSign
                    {
                    enumLiteral_2=(Token)match(input,GreaterThanSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getGREATEREnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getComparisonOpAccess().getGREATEREnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:5455:3: (enumLiteral_3= GreaterThanSignEqualsSign )
                    {
                    // InternalProblemParser.g:5455:3: (enumLiteral_3= GreaterThanSignEqualsSign )
                    // InternalProblemParser.g:5456:4: enumLiteral_3= GreaterThanSignEqualsSign
                    {
                    enumLiteral_3=(Token)match(input,GreaterThanSignEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getGREATER_EQEnumLiteralDeclaration_3().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_3, grammarAccess.getComparisonOpAccess().getGREATER_EQEnumLiteralDeclaration_3());
                      			
                    }

                    }


                    }
                    break;
                case 5 :
                    // InternalProblemParser.g:5463:3: (enumLiteral_4= EqualsSignEqualsSign )
                    {
                    // InternalProblemParser.g:5463:3: (enumLiteral_4= EqualsSignEqualsSign )
                    // InternalProblemParser.g:5464:4: enumLiteral_4= EqualsSignEqualsSign
                    {
                    enumLiteral_4=(Token)match(input,EqualsSignEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getEQEnumLiteralDeclaration_4().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_4, grammarAccess.getComparisonOpAccess().getEQEnumLiteralDeclaration_4());
                      			
                    }

                    }


                    }
                    break;
                case 6 :
                    // InternalProblemParser.g:5471:3: (enumLiteral_5= ExclamationMarkEqualsSign )
                    {
                    // InternalProblemParser.g:5471:3: (enumLiteral_5= ExclamationMarkEqualsSign )
                    // InternalProblemParser.g:5472:4: enumLiteral_5= ExclamationMarkEqualsSign
                    {
                    enumLiteral_5=(Token)match(input,ExclamationMarkEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getComparisonOpAccess().getNOT_EQEnumLiteralDeclaration_5().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_5, grammarAccess.getComparisonOpAccess().getNOT_EQEnumLiteralDeclaration_5());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleComparisonOp"


    // $ANTLR start "ruleLatticeComparisonOp"
    // InternalProblemParser.g:5482:1: ruleLatticeComparisonOp returns [Enumerator current=null] : ( (enumLiteral_0= EqualsSignEqualsSignEqualsSign ) | (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign ) | (enumLiteral_2= LessThanSignColon ) | (enumLiteral_3= ColonGreaterThanSign ) ) ;
    public final Enumerator ruleLatticeComparisonOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;
        Token enumLiteral_3=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5488:2: ( ( (enumLiteral_0= EqualsSignEqualsSignEqualsSign ) | (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign ) | (enumLiteral_2= LessThanSignColon ) | (enumLiteral_3= ColonGreaterThanSign ) ) )
            // InternalProblemParser.g:5489:2: ( (enumLiteral_0= EqualsSignEqualsSignEqualsSign ) | (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign ) | (enumLiteral_2= LessThanSignColon ) | (enumLiteral_3= ColonGreaterThanSign ) )
            {
            // InternalProblemParser.g:5489:2: ( (enumLiteral_0= EqualsSignEqualsSignEqualsSign ) | (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign ) | (enumLiteral_2= LessThanSignColon ) | (enumLiteral_3= ColonGreaterThanSign ) )
            int alt108=4;
            switch ( input.LA(1) ) {
            case EqualsSignEqualsSignEqualsSign:
                {
                alt108=1;
                }
                break;
            case ExclamationMarkEqualsSignEqualsSign:
                {
                alt108=2;
                }
                break;
            case LessThanSignColon:
                {
                alt108=3;
                }
                break;
            case ColonGreaterThanSign:
                {
                alt108=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 108, 0, input);

                throw nvae;
            }

            switch (alt108) {
                case 1 :
                    // InternalProblemParser.g:5490:3: (enumLiteral_0= EqualsSignEqualsSignEqualsSign )
                    {
                    // InternalProblemParser.g:5490:3: (enumLiteral_0= EqualsSignEqualsSignEqualsSign )
                    // InternalProblemParser.g:5491:4: enumLiteral_0= EqualsSignEqualsSignEqualsSign
                    {
                    enumLiteral_0=(Token)match(input,EqualsSignEqualsSignEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeComparisonOpAccess().getEQEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getLatticeComparisonOpAccess().getEQEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5498:3: (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign )
                    {
                    // InternalProblemParser.g:5498:3: (enumLiteral_1= ExclamationMarkEqualsSignEqualsSign )
                    // InternalProblemParser.g:5499:4: enumLiteral_1= ExclamationMarkEqualsSignEqualsSign
                    {
                    enumLiteral_1=(Token)match(input,ExclamationMarkEqualsSignEqualsSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeComparisonOpAccess().getNOT_EQEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getLatticeComparisonOpAccess().getNOT_EQEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5506:3: (enumLiteral_2= LessThanSignColon )
                    {
                    // InternalProblemParser.g:5506:3: (enumLiteral_2= LessThanSignColon )
                    // InternalProblemParser.g:5507:4: enumLiteral_2= LessThanSignColon
                    {
                    enumLiteral_2=(Token)match(input,LessThanSignColon,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeComparisonOpAccess().getSUBSETEnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getLatticeComparisonOpAccess().getSUBSETEnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:5514:3: (enumLiteral_3= ColonGreaterThanSign )
                    {
                    // InternalProblemParser.g:5514:3: (enumLiteral_3= ColonGreaterThanSign )
                    // InternalProblemParser.g:5515:4: enumLiteral_3= ColonGreaterThanSign
                    {
                    enumLiteral_3=(Token)match(input,ColonGreaterThanSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeComparisonOpAccess().getSUPERSETEnumLiteralDeclaration_3().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_3, grammarAccess.getLatticeComparisonOpAccess().getSUPERSETEnumLiteralDeclaration_3());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleLatticeComparisonOp"


    // $ANTLR start "ruleLatticeBinaryOp"
    // InternalProblemParser.g:5525:1: ruleLatticeBinaryOp returns [Enumerator current=null] : ( (enumLiteral_0= SolidusReverseSolidus ) | (enumLiteral_1= ReverseSolidusSolidus ) ) ;
    public final Enumerator ruleLatticeBinaryOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5531:2: ( ( (enumLiteral_0= SolidusReverseSolidus ) | (enumLiteral_1= ReverseSolidusSolidus ) ) )
            // InternalProblemParser.g:5532:2: ( (enumLiteral_0= SolidusReverseSolidus ) | (enumLiteral_1= ReverseSolidusSolidus ) )
            {
            // InternalProblemParser.g:5532:2: ( (enumLiteral_0= SolidusReverseSolidus ) | (enumLiteral_1= ReverseSolidusSolidus ) )
            int alt109=2;
            int LA109_0 = input.LA(1);

            if ( (LA109_0==SolidusReverseSolidus) ) {
                alt109=1;
            }
            else if ( (LA109_0==ReverseSolidusSolidus) ) {
                alt109=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 109, 0, input);

                throw nvae;
            }
            switch (alt109) {
                case 1 :
                    // InternalProblemParser.g:5533:3: (enumLiteral_0= SolidusReverseSolidus )
                    {
                    // InternalProblemParser.g:5533:3: (enumLiteral_0= SolidusReverseSolidus )
                    // InternalProblemParser.g:5534:4: enumLiteral_0= SolidusReverseSolidus
                    {
                    enumLiteral_0=(Token)match(input,SolidusReverseSolidus,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeBinaryOpAccess().getMEETEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getLatticeBinaryOpAccess().getMEETEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5541:3: (enumLiteral_1= ReverseSolidusSolidus )
                    {
                    // InternalProblemParser.g:5541:3: (enumLiteral_1= ReverseSolidusSolidus )
                    // InternalProblemParser.g:5542:4: enumLiteral_1= ReverseSolidusSolidus
                    {
                    enumLiteral_1=(Token)match(input,ReverseSolidusSolidus,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLatticeBinaryOpAccess().getJOINEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getLatticeBinaryOpAccess().getJOINEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleLatticeBinaryOp"


    // $ANTLR start "ruleAdditiveOp"
    // InternalProblemParser.g:5552:1: ruleAdditiveOp returns [Enumerator current=null] : ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) ) ;
    public final Enumerator ruleAdditiveOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5558:2: ( ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) ) )
            // InternalProblemParser.g:5559:2: ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) )
            {
            // InternalProblemParser.g:5559:2: ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) )
            int alt110=2;
            int LA110_0 = input.LA(1);

            if ( (LA110_0==PlusSign) ) {
                alt110=1;
            }
            else if ( (LA110_0==HyphenMinus) ) {
                alt110=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 110, 0, input);

                throw nvae;
            }
            switch (alt110) {
                case 1 :
                    // InternalProblemParser.g:5560:3: (enumLiteral_0= PlusSign )
                    {
                    // InternalProblemParser.g:5560:3: (enumLiteral_0= PlusSign )
                    // InternalProblemParser.g:5561:4: enumLiteral_0= PlusSign
                    {
                    enumLiteral_0=(Token)match(input,PlusSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getAdditiveOpAccess().getADDEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getAdditiveOpAccess().getADDEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5568:3: (enumLiteral_1= HyphenMinus )
                    {
                    // InternalProblemParser.g:5568:3: (enumLiteral_1= HyphenMinus )
                    // InternalProblemParser.g:5569:4: enumLiteral_1= HyphenMinus
                    {
                    enumLiteral_1=(Token)match(input,HyphenMinus,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getAdditiveOpAccess().getSUBEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getAdditiveOpAccess().getSUBEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleAdditiveOp"


    // $ANTLR start "ruleMultiplicativeOp"
    // InternalProblemParser.g:5579:1: ruleMultiplicativeOp returns [Enumerator current=null] : ( (enumLiteral_0= Asterisk ) | (enumLiteral_1= Solidus ) ) ;
    public final Enumerator ruleMultiplicativeOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5585:2: ( ( (enumLiteral_0= Asterisk ) | (enumLiteral_1= Solidus ) ) )
            // InternalProblemParser.g:5586:2: ( (enumLiteral_0= Asterisk ) | (enumLiteral_1= Solidus ) )
            {
            // InternalProblemParser.g:5586:2: ( (enumLiteral_0= Asterisk ) | (enumLiteral_1= Solidus ) )
            int alt111=2;
            int LA111_0 = input.LA(1);

            if ( (LA111_0==Asterisk) ) {
                alt111=1;
            }
            else if ( (LA111_0==Solidus) ) {
                alt111=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 111, 0, input);

                throw nvae;
            }
            switch (alt111) {
                case 1 :
                    // InternalProblemParser.g:5587:3: (enumLiteral_0= Asterisk )
                    {
                    // InternalProblemParser.g:5587:3: (enumLiteral_0= Asterisk )
                    // InternalProblemParser.g:5588:4: enumLiteral_0= Asterisk
                    {
                    enumLiteral_0=(Token)match(input,Asterisk,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getMultiplicativeOpAccess().getMULEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getMultiplicativeOpAccess().getMULEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5595:3: (enumLiteral_1= Solidus )
                    {
                    // InternalProblemParser.g:5595:3: (enumLiteral_1= Solidus )
                    // InternalProblemParser.g:5596:4: enumLiteral_1= Solidus
                    {
                    enumLiteral_1=(Token)match(input,Solidus,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getMultiplicativeOpAccess().getDIVEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getMultiplicativeOpAccess().getDIVEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleMultiplicativeOp"


    // $ANTLR start "ruleExponentialOp"
    // InternalProblemParser.g:5606:1: ruleExponentialOp returns [Enumerator current=null] : (enumLiteral_0= AsteriskAsterisk ) ;
    public final Enumerator ruleExponentialOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5612:2: ( (enumLiteral_0= AsteriskAsterisk ) )
            // InternalProblemParser.g:5613:2: (enumLiteral_0= AsteriskAsterisk )
            {
            // InternalProblemParser.g:5613:2: (enumLiteral_0= AsteriskAsterisk )
            // InternalProblemParser.g:5614:3: enumLiteral_0= AsteriskAsterisk
            {
            enumLiteral_0=(Token)match(input,AsteriskAsterisk,FOLLOW_2); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			current = grammarAccess.getExponentialOpAccess().getPOWEnumLiteralDeclaration().getEnumLiteral().getInstance();
              			newLeafNode(enumLiteral_0, grammarAccess.getExponentialOpAccess().getPOWEnumLiteralDeclaration());
              		
            }

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleExponentialOp"


    // $ANTLR start "ruleUnaryOp"
    // InternalProblemParser.g:5623:1: ruleUnaryOp returns [Enumerator current=null] : ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) ) ;
    public final Enumerator ruleUnaryOp() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5629:2: ( ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) ) )
            // InternalProblemParser.g:5630:2: ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) )
            {
            // InternalProblemParser.g:5630:2: ( (enumLiteral_0= PlusSign ) | (enumLiteral_1= HyphenMinus ) )
            int alt112=2;
            int LA112_0 = input.LA(1);

            if ( (LA112_0==PlusSign) ) {
                alt112=1;
            }
            else if ( (LA112_0==HyphenMinus) ) {
                alt112=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 112, 0, input);

                throw nvae;
            }
            switch (alt112) {
                case 1 :
                    // InternalProblemParser.g:5631:3: (enumLiteral_0= PlusSign )
                    {
                    // InternalProblemParser.g:5631:3: (enumLiteral_0= PlusSign )
                    // InternalProblemParser.g:5632:4: enumLiteral_0= PlusSign
                    {
                    enumLiteral_0=(Token)match(input,PlusSign,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getUnaryOpAccess().getPLUSEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getUnaryOpAccess().getPLUSEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5639:3: (enumLiteral_1= HyphenMinus )
                    {
                    // InternalProblemParser.g:5639:3: (enumLiteral_1= HyphenMinus )
                    // InternalProblemParser.g:5640:4: enumLiteral_1= HyphenMinus
                    {
                    enumLiteral_1=(Token)match(input,HyphenMinus,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getUnaryOpAccess().getMINUSEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getUnaryOpAccess().getMINUSEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleUnaryOp"


    // $ANTLR start "ruleConcreteness"
    // InternalProblemParser.g:5650:1: ruleConcreteness returns [Enumerator current=null] : ( (enumLiteral_0= Partial ) | (enumLiteral_1= Candidate ) ) ;
    public final Enumerator ruleConcreteness() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5656:2: ( ( (enumLiteral_0= Partial ) | (enumLiteral_1= Candidate ) ) )
            // InternalProblemParser.g:5657:2: ( (enumLiteral_0= Partial ) | (enumLiteral_1= Candidate ) )
            {
            // InternalProblemParser.g:5657:2: ( (enumLiteral_0= Partial ) | (enumLiteral_1= Candidate ) )
            int alt113=2;
            int LA113_0 = input.LA(1);

            if ( (LA113_0==Partial) ) {
                alt113=1;
            }
            else if ( (LA113_0==Candidate) ) {
                alt113=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 113, 0, input);

                throw nvae;
            }
            switch (alt113) {
                case 1 :
                    // InternalProblemParser.g:5658:3: (enumLiteral_0= Partial )
                    {
                    // InternalProblemParser.g:5658:3: (enumLiteral_0= Partial )
                    // InternalProblemParser.g:5659:4: enumLiteral_0= Partial
                    {
                    enumLiteral_0=(Token)match(input,Partial,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getConcretenessAccess().getPARTIALEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getConcretenessAccess().getPARTIALEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5666:3: (enumLiteral_1= Candidate )
                    {
                    // InternalProblemParser.g:5666:3: (enumLiteral_1= Candidate )
                    // InternalProblemParser.g:5667:4: enumLiteral_1= Candidate
                    {
                    enumLiteral_1=(Token)match(input,Candidate,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getConcretenessAccess().getCANDIDATEEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getConcretenessAccess().getCANDIDATEEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleConcreteness"


    // $ANTLR start "ruleModality"
    // InternalProblemParser.g:5677:1: ruleModality returns [Enumerator current=null] : ( (enumLiteral_0= Must ) | (enumLiteral_1= May ) ) ;
    public final Enumerator ruleModality() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5683:2: ( ( (enumLiteral_0= Must ) | (enumLiteral_1= May ) ) )
            // InternalProblemParser.g:5684:2: ( (enumLiteral_0= Must ) | (enumLiteral_1= May ) )
            {
            // InternalProblemParser.g:5684:2: ( (enumLiteral_0= Must ) | (enumLiteral_1= May ) )
            int alt114=2;
            int LA114_0 = input.LA(1);

            if ( (LA114_0==Must) ) {
                alt114=1;
            }
            else if ( (LA114_0==May) ) {
                alt114=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 114, 0, input);

                throw nvae;
            }
            switch (alt114) {
                case 1 :
                    // InternalProblemParser.g:5685:3: (enumLiteral_0= Must )
                    {
                    // InternalProblemParser.g:5685:3: (enumLiteral_0= Must )
                    // InternalProblemParser.g:5686:4: enumLiteral_0= Must
                    {
                    enumLiteral_0=(Token)match(input,Must,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getModalityAccess().getMUSTEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getModalityAccess().getMUSTEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5693:3: (enumLiteral_1= May )
                    {
                    // InternalProblemParser.g:5693:3: (enumLiteral_1= May )
                    // InternalProblemParser.g:5694:4: enumLiteral_1= May
                    {
                    enumLiteral_1=(Token)match(input,May,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getModalityAccess().getMAYEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getModalityAccess().getMAYEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleModality"


    // $ANTLR start "ruleLogicValue"
    // InternalProblemParser.g:5704:1: ruleLogicValue returns [Enumerator current=null] : ( (enumLiteral_0= True ) | (enumLiteral_1= False ) | (enumLiteral_2= Unknown ) | (enumLiteral_3= Error ) ) ;
    public final Enumerator ruleLogicValue() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;
        Token enumLiteral_2=null;
        Token enumLiteral_3=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5710:2: ( ( (enumLiteral_0= True ) | (enumLiteral_1= False ) | (enumLiteral_2= Unknown ) | (enumLiteral_3= Error ) ) )
            // InternalProblemParser.g:5711:2: ( (enumLiteral_0= True ) | (enumLiteral_1= False ) | (enumLiteral_2= Unknown ) | (enumLiteral_3= Error ) )
            {
            // InternalProblemParser.g:5711:2: ( (enumLiteral_0= True ) | (enumLiteral_1= False ) | (enumLiteral_2= Unknown ) | (enumLiteral_3= Error ) )
            int alt115=4;
            switch ( input.LA(1) ) {
            case True:
                {
                alt115=1;
                }
                break;
            case False:
                {
                alt115=2;
                }
                break;
            case Unknown:
                {
                alt115=3;
                }
                break;
            case Error:
                {
                alt115=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 115, 0, input);

                throw nvae;
            }

            switch (alt115) {
                case 1 :
                    // InternalProblemParser.g:5712:3: (enumLiteral_0= True )
                    {
                    // InternalProblemParser.g:5712:3: (enumLiteral_0= True )
                    // InternalProblemParser.g:5713:4: enumLiteral_0= True
                    {
                    enumLiteral_0=(Token)match(input,True,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLogicValueAccess().getTRUEEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getLogicValueAccess().getTRUEEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5720:3: (enumLiteral_1= False )
                    {
                    // InternalProblemParser.g:5720:3: (enumLiteral_1= False )
                    // InternalProblemParser.g:5721:4: enumLiteral_1= False
                    {
                    enumLiteral_1=(Token)match(input,False,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLogicValueAccess().getFALSEEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getLogicValueAccess().getFALSEEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalProblemParser.g:5728:3: (enumLiteral_2= Unknown )
                    {
                    // InternalProblemParser.g:5728:3: (enumLiteral_2= Unknown )
                    // InternalProblemParser.g:5729:4: enumLiteral_2= Unknown
                    {
                    enumLiteral_2=(Token)match(input,Unknown,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLogicValueAccess().getUNKNOWNEnumLiteralDeclaration_2().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_2, grammarAccess.getLogicValueAccess().getUNKNOWNEnumLiteralDeclaration_2());
                      			
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalProblemParser.g:5736:3: (enumLiteral_3= Error )
                    {
                    // InternalProblemParser.g:5736:3: (enumLiteral_3= Error )
                    // InternalProblemParser.g:5737:4: enumLiteral_3= Error
                    {
                    enumLiteral_3=(Token)match(input,Error,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getLogicValueAccess().getERROREnumLiteralDeclaration_3().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_3, grammarAccess.getLogicValueAccess().getERROREnumLiteralDeclaration_3());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleLogicValue"


    // $ANTLR start "ruleShortLogicValue"
    // InternalProblemParser.g:5747:1: ruleShortLogicValue returns [Enumerator current=null] : ( (enumLiteral_0= ExclamationMark ) | (enumLiteral_1= QuestionMark ) ) ;
    public final Enumerator ruleShortLogicValue() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5753:2: ( ( (enumLiteral_0= ExclamationMark ) | (enumLiteral_1= QuestionMark ) ) )
            // InternalProblemParser.g:5754:2: ( (enumLiteral_0= ExclamationMark ) | (enumLiteral_1= QuestionMark ) )
            {
            // InternalProblemParser.g:5754:2: ( (enumLiteral_0= ExclamationMark ) | (enumLiteral_1= QuestionMark ) )
            int alt116=2;
            int LA116_0 = input.LA(1);

            if ( (LA116_0==ExclamationMark) ) {
                alt116=1;
            }
            else if ( (LA116_0==QuestionMark) ) {
                alt116=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 116, 0, input);

                throw nvae;
            }
            switch (alt116) {
                case 1 :
                    // InternalProblemParser.g:5755:3: (enumLiteral_0= ExclamationMark )
                    {
                    // InternalProblemParser.g:5755:3: (enumLiteral_0= ExclamationMark )
                    // InternalProblemParser.g:5756:4: enumLiteral_0= ExclamationMark
                    {
                    enumLiteral_0=(Token)match(input,ExclamationMark,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getShortLogicValueAccess().getFALSEEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getShortLogicValueAccess().getFALSEEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5763:3: (enumLiteral_1= QuestionMark )
                    {
                    // InternalProblemParser.g:5763:3: (enumLiteral_1= QuestionMark )
                    // InternalProblemParser.g:5764:4: enumLiteral_1= QuestionMark
                    {
                    enumLiteral_1=(Token)match(input,QuestionMark,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getShortLogicValueAccess().getUNKNOWNEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getShortLogicValueAccess().getUNKNOWNEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleShortLogicValue"


    // $ANTLR start "ruleNodeKind"
    // InternalProblemParser.g:5774:1: ruleNodeKind returns [Enumerator current=null] : ( (enumLiteral_0= Atom ) | (enumLiteral_1= Multi ) ) ;
    public final Enumerator ruleNodeKind() throws RecognitionException {
        Enumerator current = null;

        Token enumLiteral_0=null;
        Token enumLiteral_1=null;


        	enterRule();

        try {
            // InternalProblemParser.g:5780:2: ( ( (enumLiteral_0= Atom ) | (enumLiteral_1= Multi ) ) )
            // InternalProblemParser.g:5781:2: ( (enumLiteral_0= Atom ) | (enumLiteral_1= Multi ) )
            {
            // InternalProblemParser.g:5781:2: ( (enumLiteral_0= Atom ) | (enumLiteral_1= Multi ) )
            int alt117=2;
            int LA117_0 = input.LA(1);

            if ( (LA117_0==Atom) ) {
                alt117=1;
            }
            else if ( (LA117_0==Multi) ) {
                alt117=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 117, 0, input);

                throw nvae;
            }
            switch (alt117) {
                case 1 :
                    // InternalProblemParser.g:5782:3: (enumLiteral_0= Atom )
                    {
                    // InternalProblemParser.g:5782:3: (enumLiteral_0= Atom )
                    // InternalProblemParser.g:5783:4: enumLiteral_0= Atom
                    {
                    enumLiteral_0=(Token)match(input,Atom,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getNodeKindAccess().getATOMEnumLiteralDeclaration_0().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_0, grammarAccess.getNodeKindAccess().getATOMEnumLiteralDeclaration_0());
                      			
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalProblemParser.g:5790:3: (enumLiteral_1= Multi )
                    {
                    // InternalProblemParser.g:5790:3: (enumLiteral_1= Multi )
                    // InternalProblemParser.g:5791:4: enumLiteral_1= Multi
                    {
                    enumLiteral_1=(Token)match(input,Multi,FOLLOW_2); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      				current = grammarAccess.getNodeKindAccess().getMULTIEnumLiteralDeclaration_1().getEnumLiteral().getInstance();
                      				newLeafNode(enumLiteral_1, grammarAccess.getNodeKindAccess().getMULTIEnumLiteralDeclaration_1());
                      			
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {

              	leaveRule();

            }
        }

            catch (RecognitionException re) {
                recover(input,re);
                appendSkippedTokens();
            }
        finally {
        }
        return current;
    }
    // $ANTLR end "ruleNodeKind"

    // $ANTLR start synpred1_InternalProblemParser
    public final void synpred1_InternalProblemParser_fragment() throws RecognitionException {   
        // InternalProblemParser.g:3635:6: ( ( ruleModality ) )
        // InternalProblemParser.g:3635:7: ( ruleModality )
        {
        // InternalProblemParser.g:3635:7: ( ruleModality )
        // InternalProblemParser.g:3636:7: ruleModality
        {
        pushFollow(FOLLOW_2);
        ruleModality();

        state._fsp--;
        if (state.failed) return ;

        }


        }
    }
    // $ANTLR end synpred1_InternalProblemParser

    // $ANTLR start synpred2_InternalProblemParser
    public final void synpred2_InternalProblemParser_fragment() throws RecognitionException {   
        // InternalProblemParser.g:3680:6: ( ( ruleConcreteness ) )
        // InternalProblemParser.g:3680:7: ( ruleConcreteness )
        {
        // InternalProblemParser.g:3680:7: ( ruleConcreteness )
        // InternalProblemParser.g:3681:7: ruleConcreteness
        {
        pushFollow(FOLLOW_2);
        ruleConcreteness();

        state._fsp--;
        if (state.failed) return ;

        }


        }
    }
    // $ANTLR end synpred2_InternalProblemParser

    // Delegated rules

    public final boolean synpred1_InternalProblemParser() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred1_InternalProblemParser_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }
    public final boolean synpred2_InternalProblemParser() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred2_InternalProblemParser_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }


    protected DFA2 dfa2 = new DFA2(this);
    protected DFA4 dfa4 = new DFA4(this);
    protected DFA43 dfa43 = new DFA43(this);
    protected DFA26 dfa26 = new DFA26(this);
    protected DFA48 dfa48 = new DFA48(this);
    protected DFA56 dfa56 = new DFA56(this);
    protected DFA58 dfa58 = new DFA58(this);
    protected DFA63 dfa63 = new DFA63(this);
    protected DFA72 dfa72 = new DFA72(this);
    protected DFA86 dfa86 = new DFA86(this);
    static final String dfa_1s = "\30\uffff";
    static final String dfa_2s = "\1\3\27\uffff";
    static final String dfa_3s = "\3\4\1\uffff\23\77\1\uffff";
    static final String dfa_4s = "\3\131\1\uffff\23\123\1\uffff";
    static final String dfa_5s = "\3\uffff\1\2\23\uffff\1\1";
    static final String dfa_6s = "\30\uffff}>";
    static final String[] dfa_7s = {
            "\3\3\1\uffff\11\3\2\uffff\1\1\1\3\1\uffff\2\3\1\2\1\uffff\3\3\1\uffff\4\3\1\uffff\2\3\15\uffff\1\3\7\uffff\1\3\2\uffff\2\3\15\uffff\2\3\6\uffff\1\3\4\uffff\1\3",
            "\1\20\1\17\1\14\1\uffff\1\24\1\15\1\uffff\1\23\1\13\1\16\1\25\4\uffff\1\11\1\26\1\uffff\1\22\1\uffff\1\12\1\uffff\1\21\3\uffff\1\10\1\uffff\1\7\21\uffff\1\27\7\uffff\1\6\4\uffff\1\3\5\uffff\1\27\15\uffff\1\3\1\4\4\uffff\1\5",
            "\1\20\1\17\1\14\1\uffff\1\24\1\15\1\uffff\1\23\1\13\1\16\1\25\4\uffff\1\11\1\26\1\uffff\1\22\1\uffff\1\12\1\uffff\1\21\3\uffff\1\10\1\uffff\1\7\21\uffff\1\27\7\uffff\1\6\4\uffff\1\3\5\uffff\1\27\15\uffff\1\3\1\4\4\uffff\1\5",
            "",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            "\1\3\5\uffff\1\27\15\uffff\1\27",
            ""
    };

    static final short[] dfa_1 = DFA.unpackEncodedString(dfa_1s);
    static final short[] dfa_2 = DFA.unpackEncodedString(dfa_2s);
    static final char[] dfa_3 = DFA.unpackEncodedStringToUnsignedChars(dfa_3s);
    static final char[] dfa_4 = DFA.unpackEncodedStringToUnsignedChars(dfa_4s);
    static final short[] dfa_5 = DFA.unpackEncodedString(dfa_5s);
    static final short[] dfa_6 = DFA.unpackEncodedString(dfa_6s);
    static final short[][] dfa_7 = unpackEncodedStringArray(dfa_7s);

    class DFA2 extends DFA {

        public DFA2(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 2;
            this.eot = dfa_1;
            this.eof = dfa_2;
            this.min = dfa_3;
            this.max = dfa_4;
            this.accept = dfa_5;
            this.special = dfa_6;
            this.transition = dfa_7;
        }
        public String getDescription() {
            return "73:3: ( ( (lv_kind_0_0= ruleModuleKind ) ) ( (lv_name_1_0= ruleQualifiedName ) )? otherlv_2= FullStop )?";
        }
    }
    static final String dfa_8s = "\70\uffff";
    static final String dfa_9s = "\1\4\2\uffff\24\4\1\uffff\1\4\1\uffff\11\4\1\uffff\24\4";
    static final String dfa_10s = "\1\131\2\uffff\24\131\1\uffff\1\131\1\uffff\11\131\1\uffff\24\131";
    static final String dfa_11s = "\1\uffff\1\1\1\2\24\uffff\1\3\1\uffff\1\4\11\uffff\1\5\24\uffff";
    static final String dfa_12s = "\70\uffff}>";
    static final String[] dfa_13s = {
            "\1\20\1\17\1\14\1\uffff\1\24\1\15\1\27\1\23\1\13\1\16\1\25\1\27\1\2\2\uffff\1\11\1\26\1\uffff\1\22\1\1\1\12\1\uffff\1\21\2\27\1\uffff\1\10\1\31\1\7\1\27\1\uffff\2\27\15\uffff\1\3\7\uffff\1\6\2\uffff\1\2\1\30\15\uffff\1\2\1\27\6\uffff\1\4\4\uffff\1\5",
            "",
            "",
            "\1\36\1\35\1\14\1\uffff\1\24\1\15\1\uffff\1\23\1\13\1\34\1\25\4\uffff\1\11\1\26\1\uffff\1\22\1\uffff\1\12\1\uffff\1\37\3\uffff\1\33\1\uffff\1\32\31\uffff\1\6\31\uffff\1\4\4\uffff\1\5",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\15\uffff\1\27\5\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\15\uffff\1\27\5\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\3\uffff\1\27\25\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\3\uffff\1\27\25\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\3\uffff\1\27\25\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\2\uffff\1\27\16\uffff\1\27\7\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "",
            "\2\43\1\44\1\uffff\1\43\1\42\1\uffff\1\43\1\41\2\43\4\uffff\2\43\1\uffff\1\43\1\uffff\1\43\1\uffff\1\43\3\uffff\1\43\1\uffff\1\43\2\uffff\1\27\16\uffff\1\43\7\uffff\1\43\31\uffff\1\43\4\uffff\1\43",
            "",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\1\61\1\60\1\55\1\uffff\1\65\1\56\1\uffff\1\64\1\54\1\57\1\66\4\uffff\1\52\1\67\1\uffff\1\63\1\uffff\1\53\1\uffff\1\62\3\uffff\1\51\1\uffff\1\50\31\uffff\1\47\31\uffff\1\45\4\uffff\1\46",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\43\5\uffff\1\43\15\uffff\1\43\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\43\5\uffff\1\43\15\uffff\1\43\1\27\4\uffff\1\27",
            "",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\43\5\uffff\1\43\15\uffff\1\43\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27",
            "\3\27\1\uffff\2\27\1\uffff\4\27\4\uffff\2\27\1\uffff\1\27\1\uffff\1\27\1\uffff\1\27\3\uffff\1\27\1\uffff\1\27\31\uffff\1\27\4\uffff\1\2\23\uffff\1\40\1\27\4\uffff\1\27"
    };

    static final short[] dfa_8 = DFA.unpackEncodedString(dfa_8s);
    static final char[] dfa_9 = DFA.unpackEncodedStringToUnsignedChars(dfa_9s);
    static final char[] dfa_10 = DFA.unpackEncodedStringToUnsignedChars(dfa_10s);
    static final short[] dfa_11 = DFA.unpackEncodedString(dfa_11s);
    static final short[] dfa_12 = DFA.unpackEncodedString(dfa_12s);
    static final short[][] dfa_13 = unpackEncodedStringArray(dfa_13s);

    class DFA4 extends DFA {

        public DFA4(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 4;
            this.eot = dfa_8;
            this.eof = dfa_8;
            this.min = dfa_9;
            this.max = dfa_10;
            this.accept = dfa_11;
            this.special = dfa_12;
            this.transition = dfa_13;
        }
        public String getDescription() {
            return "154:2: (this_ImportStatement_0= ruleImportStatement | this_Assertion_1= ruleAssertion | this_AnnotatedStatement_2= ruleAnnotatedStatement | this_ScopeDeclaration_3= ruleScopeDeclaration | this_TopLevelAnnotation_4= ruleTopLevelAnnotation )";
        }
    }
    static final String dfa_14s = "\45\uffff";
    static final String dfa_15s = "\1\4\2\uffff\1\6\1\uffff\1\4\1\uffff\5\4\6\uffff\23\77";
    static final String dfa_16s = "\1\131\2\uffff\1\43\1\uffff\1\131\1\uffff\5\131\6\uffff\23\105";
    static final String dfa_17s = "\1\uffff\1\1\1\2\1\uffff\1\6\1\uffff\1\7\5\uffff\1\10\1\12\1\4\1\3\1\5\1\11\23\uffff";
    static final String dfa_18s = "\45\uffff}>";
    static final String[] dfa_19s = {
            "\1\13\1\12\1\6\1\uffff\2\6\1\1\2\6\1\11\1\6\1\15\3\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff\1\5\1\1\1\4\1\uffff\1\10\1\uffff\1\7\1\2\1\uffff\1\4\1\14\15\uffff\1\6\7\uffff\1\6\3\uffff\1\3\25\uffff\1\6\4\uffff\1\6",
            "",
            "",
            "\1\16\2\uffff\1\20\2\uffff\1\17\26\uffff\1\21",
            "",
            "\3\6\1\uffff\2\6\1\uffff\4\6\4\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff\1\6\3\uffff\1\6\1\uffff\1\6\2\uffff\1\4\16\uffff\1\6\7\uffff\1\6\30\uffff\2\6\4\uffff\1\6",
            "",
            "\1\36\1\35\1\32\1\uffff\1\42\1\33\1\uffff\1\41\1\31\1\34\1\43\4\uffff\1\27\1\44\1\uffff\1\40\1\uffff\1\30\1\uffff\1\37\3\uffff\1\26\1\uffff\1\25\31\uffff\1\24\22\uffff\1\15\5\uffff\1\6\1\22\4\uffff\1\23",
            "\1\36\1\35\1\32\1\uffff\1\42\1\33\1\uffff\1\41\1\31\1\34\1\43\4\uffff\1\27\1\44\1\uffff\1\40\1\uffff\1\30\1\uffff\1\37\3\uffff\1\26\1\uffff\1\25\31\uffff\1\24\22\uffff\1\15\5\uffff\1\6\1\22\4\uffff\1\23",
            "\3\6\1\uffff\2\6\1\uffff\4\6\4\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff\1\6\3\uffff\1\6\1\uffff\1\6\3\uffff\1\14\25\uffff\1\6\30\uffff\2\6\4\uffff\1\6",
            "\3\6\1\uffff\2\6\1\uffff\4\6\4\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff\1\6\3\uffff\1\6\1\uffff\1\6\3\uffff\1\14\25\uffff\1\6\30\uffff\2\6\4\uffff\1\6",
            "\3\6\1\uffff\2\6\1\uffff\4\6\4\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff\1\6\3\uffff\1\6\1\uffff\1\6\3\uffff\1\14\25\uffff\1\6\30\uffff\2\6\4\uffff\1\6",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15",
            "\1\6\3\uffff\1\15\1\uffff\1\15"
    };

    static final short[] dfa_14 = DFA.unpackEncodedString(dfa_14s);
    static final char[] dfa_15 = DFA.unpackEncodedStringToUnsignedChars(dfa_15s);
    static final char[] dfa_16 = DFA.unpackEncodedStringToUnsignedChars(dfa_16s);
    static final short[] dfa_17 = DFA.unpackEncodedString(dfa_17s);
    static final short[] dfa_18 = DFA.unpackEncodedString(dfa_18s);
    static final short[][] dfa_19 = unpackEncodedStringArray(dfa_19s);

    class DFA43 extends DFA {

        public DFA43(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 43;
            this.eot = dfa_14;
            this.eof = dfa_14;
            this.min = dfa_15;
            this.max = dfa_16;
            this.accept = dfa_17;
            this.special = dfa_18;
            this.transition = dfa_19;
        }
        public String getDescription() {
            return "226:3: ( ( () ( (lv_abstract_2_0= Abstract ) )? otherlv_3= Class ( (lv_name_4_0= ruleIdentifier ) ) (otherlv_5= Extends ( ( ruleQualifiedName ) ) (otherlv_7= Comma ( ( ruleQualifiedName ) ) )* )? ( (otherlv_9= LeftCurlyBracket ( ( (lv_featureDeclarations_10_0= ruleReferenceDeclaration ) ) (otherlv_11= Semicolon )? )* otherlv_12= RightCurlyBracket ) | otherlv_13= FullStop ) ) | ( () otherlv_15= Enum ( (lv_name_16_0= ruleIdentifier ) ) ( (otherlv_17= LeftCurlyBracket ( ( (lv_literals_18_0= ruleEnumLiteral ) ) (otherlv_19= Comma ( (lv_literals_20_0= ruleEnumLiteral ) ) )* (otherlv_21= Comma | otherlv_22= Semicolon )? )? otherlv_23= RightCurlyBracket ) | otherlv_24= FullStop ) ) | ( () otherlv_26= NumberSign otherlv_27= Datatype ( (lv_name_28_0= ruleIdentifier ) ) otherlv_29= FullStop ) | ( () otherlv_31= NumberSign otherlv_32= Aggregator ( (lv_name_33_0= ruleIdentifier ) ) otherlv_34= FullStop ) | ( () otherlv_36= NumberSign otherlv_37= Primitive ( (lv_shadow_38_0= Shadow ) )? ( (lv_name_39_0= ruleIdentifier ) ) otherlv_40= LeftParenthesis ( ( (lv_parameters_41_0= ruleParameter ) ) (otherlv_42= Comma ( (lv_parameters_43_0= ruleParameter ) ) )* )? otherlv_44= RightParenthesis otherlv_45= FullStop ) | ( () ( ( (lv_kind_47_0= ruleErrorPredicateKind ) ) | ( ( (lv_kind_48_0= rulePredicateKind ) )? otherlv_49= Pred ) ) ( (lv_name_50_0= ruleIdentifier ) ) otherlv_51= LeftParenthesis ( ( (lv_parameters_52_0= ruleParameter ) ) (otherlv_53= Comma ( (lv_parameters_54_0= ruleParameter ) ) )* )? otherlv_55= RightParenthesis (otherlv_56= Subsets ( ( ruleQualifiedName ) ) (otherlv_58= Comma ( ( ruleQualifiedName ) ) )* )? (otherlv_60= LessThanSignHyphenMinusGreaterThanSign ( (lv_bodies_61_0= ruleConjunction ) ) (otherlv_62= Semicolon ( (lv_bodies_63_0= ruleConjunction ) ) )* )? otherlv_64= FullStop ) | ( () ( (lv_shadow_66_0= Shadow ) )? ( ( ruleQualifiedName ) ) ( (lv_name_68_0= ruleIdentifier ) ) otherlv_69= LeftParenthesis ( ( (lv_parameters_70_0= ruleParameter ) ) (otherlv_71= Comma ( (lv_parameters_72_0= ruleParameter ) ) )* )? otherlv_73= RightParenthesis (otherlv_74= EqualsSign ( (lv_cases_75_0= ruleCase ) ) (otherlv_76= Semicolon ( (lv_cases_77_0= ruleCase ) ) )* )? otherlv_78= FullStop ) | ( () ( (lv_kind_80_0= ruleRuleKind ) )? otherlv_81= Rule ( (lv_name_82_0= ruleIdentifier ) ) otherlv_83= LeftParenthesis ( ( (lv_parameters_84_0= ruleParameter ) ) (otherlv_85= Comma ( (lv_parameters_86_0= ruleParameter ) ) )* )? otherlv_87= RightParenthesis (otherlv_88= LessThanSignHyphenMinusGreaterThanSign ( (lv_preconditions_89_0= ruleConjunction ) ) (otherlv_90= Semicolon ( (lv_preconditions_91_0= ruleConjunction ) ) )* )? (otherlv_92= EqualsSignEqualsSignGreaterThanSign ( (lv_consequents_93_0= ruleConsequent ) ) (otherlv_94= Semicolon ( (lv_consequents_95_0= ruleConsequent ) ) )* )? otherlv_96= FullStop ) | ( () otherlv_98= NumberSign otherlv_99= Pred ( (lv_name_100_0= ruleIdentifier ) ) otherlv_101= LeftParenthesis ( ( (lv_parameters_102_0= ruleParameter ) ) (otherlv_103= Comma ( (lv_parameters_104_0= ruleParameter ) ) )* )? otherlv_105= RightParenthesis otherlv_106= FullStop ) | ( () (otherlv_108= Declare | ( (otherlv_109= Declare )? ( (lv_kind_110_0= ruleNodeKind ) ) ) ) ( (lv_nodes_111_0= ruleEnumLiteral ) ) (otherlv_112= Comma ( (lv_nodes_113_0= ruleEnumLiteral ) ) )* otherlv_114= FullStop ) )";
        }
    }
    static final String dfa_20s = "\27\uffff";
    static final String dfa_21s = "\2\4\2\uffff\23\4";
    static final String dfa_22s = "\2\131\2\uffff\23\131";
    static final String dfa_23s = "\2\uffff\1\2\1\1\23\uffff";
    static final String dfa_24s = "\27\uffff}>";
    static final String[] dfa_25s = {
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\1\3\uffff\1\2\1\uffff\1\2\21\uffff\1\2\7\uffff\1\2\31\uffff\1\2\4\uffff\1\2",
            "\1\20\1\17\1\14\1\uffff\1\24\1\15\1\uffff\1\23\1\13\1\16\1\25\4\uffff\1\11\1\26\1\uffff\1\22\1\uffff\1\12\1\uffff\1\21\3\uffff\1\10\1\uffff\1\7\21\uffff\1\3\7\uffff\1\6\30\uffff\1\2\1\4\4\uffff\1\5",
            "",
            "",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3",
            "\3\3\1\uffff\2\3\1\uffff\4\3\4\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\1\3\3\uffff\1\3\1\uffff\1\3\31\uffff\1\3\4\uffff\1\2\23\uffff\2\3\4\uffff\1\3"
    };

    static final short[] dfa_20 = DFA.unpackEncodedString(dfa_20s);
    static final char[] dfa_21 = DFA.unpackEncodedStringToUnsignedChars(dfa_21s);
    static final char[] dfa_22 = DFA.unpackEncodedStringToUnsignedChars(dfa_22s);
    static final short[] dfa_23 = DFA.unpackEncodedString(dfa_23s);
    static final short[] dfa_24 = DFA.unpackEncodedString(dfa_24s);
    static final short[][] dfa_25 = unpackEncodedStringArray(dfa_25s);

    class DFA26 extends DFA {

        public DFA26(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 26;
            this.eot = dfa_20;
            this.eof = dfa_20;
            this.min = dfa_21;
            this.max = dfa_22;
            this.accept = dfa_23;
            this.special = dfa_24;
            this.transition = dfa_25;
        }
        public String getDescription() {
            return "896:5: ( (lv_shadow_66_0= Shadow ) )?";
        }
    }
    static final String dfa_26s = "\26\uffff";
    static final String dfa_27s = "\1\uffff\23\24\2\uffff";
    static final String dfa_28s = "\1\4\23\46\2\uffff";
    static final String dfa_29s = "\1\131\23\123\2\uffff";
    static final String dfa_30s = "\24\uffff\1\2\1\1";
    static final String dfa_31s = "\26\uffff}>";
    static final String[] dfa_32s = {
            "\1\15\1\14\1\11\1\24\1\21\1\12\1\uffff\1\20\1\10\1\13\1\22\3\uffff\1\24\1\6\1\23\1\24\1\17\1\uffff\1\7\1\uffff\1\16\1\uffff\2\24\1\5\1\uffff\1\4\1\uffff\1\24\2\uffff\1\24\4\uffff\1\24\7\uffff\1\24\7\uffff\1\3\2\uffff\1\24\1\uffff\1\24\1\uffff\2\24\1\uffff\1\24\17\uffff\1\1\2\24\1\uffff\1\24\1\2",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "\1\24\1\uffff\1\24\2\uffff\3\24\2\uffff\2\24\1\uffff\7\24\1\uffff\2\24\2\uffff\6\24\1\uffff\1\24\2\uffff\1\24\1\25\1\24\4\uffff\1\24\1\uffff\2\24",
            "",
            ""
    };

    static final short[] dfa_26 = DFA.unpackEncodedString(dfa_26s);
    static final short[] dfa_27 = DFA.unpackEncodedString(dfa_27s);
    static final char[] dfa_28 = DFA.unpackEncodedStringToUnsignedChars(dfa_28s);
    static final char[] dfa_29 = DFA.unpackEncodedStringToUnsignedChars(dfa_29s);
    static final short[] dfa_30 = DFA.unpackEncodedString(dfa_30s);
    static final short[] dfa_31 = DFA.unpackEncodedString(dfa_31s);
    static final short[][] dfa_32 = unpackEncodedStringArray(dfa_32s);

    class DFA48 extends DFA {

        public DFA48(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 48;
            this.eot = dfa_26;
            this.eof = dfa_27;
            this.min = dfa_28;
            this.max = dfa_29;
            this.accept = dfa_30;
            this.special = dfa_31;
            this.transition = dfa_32;
        }
        public String getDescription() {
            return "1673:3: ( ( ( ruleIdentifier ) ) otherlv_2= EqualsSign )?";
        }
    }
    static final String dfa_33s = "\3\uffff\23\26\1\uffff";
    static final String dfa_34s = "\1\4\2\uffff\23\4\1\uffff";
    static final String dfa_35s = "\1\131\2\uffff\23\131\1\uffff";
    static final String dfa_36s = "\1\uffff\1\1\1\2\23\uffff\1\3";
    static final String[] dfa_37s = {
            "\1\17\1\16\1\13\1\uffff\1\23\1\14\1\uffff\1\22\1\12\1\15\1\24\4\uffff\1\10\1\25\1\uffff\1\21\1\uffff\1\11\1\uffff\1\20\3\uffff\1\7\1\uffff\1\6\2\uffff\1\1\16\uffff\1\2\7\uffff\1\5\31\uffff\1\3\4\uffff\1\4",
            "",
            "",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            "\3\2\1\uffff\2\2\1\uffff\4\2\4\uffff\2\2\1\uffff\1\2\1\uffff\1\2\1\uffff\1\2\3\uffff\1\2\1\uffff\1\2\31\uffff\1\2\5\uffff\1\26\2\uffff\1\26\17\uffff\2\2\4\uffff\1\2",
            ""
    };
    static final short[] dfa_33 = DFA.unpackEncodedString(dfa_33s);
    static final char[] dfa_34 = DFA.unpackEncodedStringToUnsignedChars(dfa_34s);
    static final char[] dfa_35 = DFA.unpackEncodedStringToUnsignedChars(dfa_35s);
    static final short[] dfa_36 = DFA.unpackEncodedString(dfa_36s);
    static final short[][] dfa_37 = unpackEncodedStringArray(dfa_37s);

    class DFA56 extends DFA {

        public DFA56(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 56;
            this.eot = dfa_20;
            this.eof = dfa_33;
            this.min = dfa_34;
            this.max = dfa_35;
            this.accept = dfa_36;
            this.special = dfa_24;
            this.transition = dfa_37;
        }
        public String getDescription() {
            return "2267:3: ( ( (lv_kind_1_0= ruleParameterKind ) ) | ( ( ruleQualifiedName ) ) )?";
        }
    }
    static final String dfa_38s = "\57\uffff";
    static final String dfa_39s = "\1\4\1\uffff\1\4\1\uffff\2\4\24\46\1\4\1\uffff\23\46";
    static final String dfa_40s = "\1\131\1\uffff\1\131\1\uffff\2\131\23\123\1\113\1\131\1\uffff\23\123";
    static final String dfa_41s = "\1\uffff\1\1\1\uffff\1\2\27\uffff\1\1\23\uffff";
    static final String dfa_42s = "\57\uffff}>";
    static final String[] dfa_43s = {
            "\3\1\1\uffff\2\1\1\uffff\4\1\4\uffff\2\1\1\uffff\1\2\1\uffff\1\1\1\uffff\1\1\3\uffff\1\1\1\uffff\1\1\21\uffff\1\1\7\uffff\1\1\2\uffff\1\1\16\uffff\1\1\7\uffff\1\1\4\uffff\1\1",
            "",
            "\6\3\1\uffff\4\3\3\uffff\5\3\1\uffff\1\3\1\uffff\1\3\1\uffff\3\3\1\uffff\1\3\1\uffff\1\3\2\uffff\1\3\4\uffff\1\3\7\uffff\1\3\7\uffff\1\3\2\uffff\1\3\1\uffff\1\4\1\uffff\2\3\1\uffff\1\3\16\uffff\1\1\3\3\1\uffff\2\3",
            "",
            "\1\22\1\21\1\16\1\3\1\26\1\17\1\uffff\1\25\1\15\1\20\1\27\3\uffff\1\3\1\13\1\30\1\3\1\24\1\uffff\1\14\1\uffff\1\23\1\uffff\2\3\1\12\1\uffff\1\11\1\uffff\1\3\2\uffff\1\3\4\uffff\1\3\7\uffff\1\5\7\uffff\1\10\2\uffff\1\3\1\uffff\1\3\1\1\1\31\1\3\1\uffff\1\3\17\uffff\1\6\2\3\1\uffff\1\3\1\7",
            "\1\22\1\21\1\16\1\uffff\1\26\1\17\1\uffff\1\25\1\15\1\20\1\27\4\uffff\1\13\1\30\1\uffff\1\24\1\uffff\1\14\1\uffff\1\23\3\uffff\1\12\1\uffff\1\11\31\uffff\1\10\31\uffff\1\6\4\uffff\1\7",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\1\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\3\uffff\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3",
            "\1\50\1\47\1\44\1\uffff\1\54\1\45\1\uffff\1\53\1\43\1\46\1\55\4\uffff\1\41\1\56\1\uffff\1\52\1\uffff\1\42\1\uffff\1\51\3\uffff\1\40\1\uffff\1\37\31\uffff\1\36\31\uffff\1\34\4\uffff\1\35",
            "",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32",
            "\1\3\1\uffff\1\3\2\uffff\3\3\2\uffff\2\3\1\uffff\7\3\1\uffff\2\3\2\uffff\1\3\1\33\2\3\1\33\1\3\1\uffff\1\3\2\uffff\1\3\1\uffff\1\3\4\uffff\1\3\1\uffff\1\3\1\32"
    };

    static final short[] dfa_38 = DFA.unpackEncodedString(dfa_38s);
    static final char[] dfa_39 = DFA.unpackEncodedStringToUnsignedChars(dfa_39s);
    static final char[] dfa_40 = DFA.unpackEncodedStringToUnsignedChars(dfa_40s);
    static final short[] dfa_41 = DFA.unpackEncodedString(dfa_41s);
    static final short[] dfa_42 = DFA.unpackEncodedString(dfa_42s);
    static final short[][] dfa_43 = unpackEncodedStringArray(dfa_43s);

    class DFA58 extends DFA {

        public DFA58(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 58;
            this.eot = dfa_38;
            this.eof = dfa_38;
            this.min = dfa_39;
            this.max = dfa_40;
            this.accept = dfa_41;
            this.special = dfa_42;
            this.transition = dfa_43;
        }
        public String getDescription() {
            return "2405:2: (this_AssertionAction_0= ruleAssertionAction | this_TheoryAction_1= ruleTheoryAction )";
        }
    }
    static final String dfa_44s = "\u0080\uffff";
    static final String dfa_45s = "\100\uffff\1\25\77\uffff";
    static final String dfa_46s = "\2\4\23\77\1\uffff\2\4\23\77\1\4\24\100\1\103\2\4\1\uffff\23\100\1\4\24\100\1\4\23\100";
    static final String dfa_47s = "\2\131\23\123\1\uffff\2\131\23\123\1\131\23\123\1\103\1\110\2\131\1\uffff\23\123\1\131\23\123\1\103\1\131\23\123";
    static final String dfa_48s = "\25\uffff\1\2\55\uffff\1\1\74\uffff";
    static final String dfa_49s = "\u0080\uffff}>";
    static final String[] dfa_50s = {
            "\1\16\1\15\1\12\1\uffff\1\22\1\13\1\uffff\1\21\1\11\1\14\1\23\4\uffff\1\7\1\24\1\uffff\1\20\1\uffff\1\10\1\uffff\1\17\3\uffff\1\6\1\uffff\1\5\21\uffff\1\1\7\uffff\1\4\2\uffff\1\25\16\uffff\1\25\7\uffff\1\2\4\uffff\1\3",
            "\1\16\1\15\1\12\1\uffff\1\22\1\13\1\uffff\1\21\1\11\1\14\1\23\4\uffff\1\7\1\24\1\uffff\1\20\1\uffff\1\10\1\uffff\1\17\3\uffff\1\6\1\uffff\1\5\31\uffff\1\4\31\uffff\1\2\4\uffff\1\3",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "",
            "\1\44\1\43\1\40\1\uffff\1\50\1\41\1\uffff\1\47\1\37\1\42\1\51\4\uffff\1\35\1\52\1\uffff\1\46\1\uffff\1\36\1\uffff\1\45\3\uffff\1\34\1\uffff\1\33\31\uffff\1\32\31\uffff\1\30\4\uffff\1\31",
            "\1\70\1\67\1\64\1\uffff\1\74\1\65\1\uffff\1\73\1\63\1\66\1\75\4\uffff\1\61\1\76\1\uffff\1\72\1\uffff\1\62\1\uffff\1\71\3\uffff\1\60\1\uffff\1\57\21\uffff\1\53\7\uffff\1\56\5\uffff\1\100\1\77\22\uffff\1\54\4\uffff\1\55",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\70\1\67\1\64\1\uffff\1\74\1\65\1\uffff\1\73\1\63\1\66\1\75\4\uffff\1\61\1\76\1\uffff\1\72\1\uffff\1\62\1\uffff\1\71\3\uffff\1\60\1\uffff\1\57\31\uffff\1\56\31\uffff\1\54\4\uffff\1\55",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102",
            "\1\25\1\uffff\1\25\1\uffff\1\103\1\25",
            "\1\120\1\117\1\114\1\uffff\1\124\1\115\1\uffff\1\123\1\113\1\116\1\125\4\uffff\1\111\1\126\1\uffff\1\122\1\uffff\1\112\1\uffff\1\121\3\uffff\1\110\1\uffff\1\107\31\uffff\1\106\31\uffff\1\104\4\uffff\1\105",
            "\1\144\1\143\1\140\1\uffff\1\150\1\141\1\uffff\1\147\1\137\1\142\1\151\4\uffff\1\135\1\152\1\uffff\1\146\1\uffff\1\136\1\uffff\1\145\3\uffff\1\134\1\uffff\1\133\21\uffff\1\127\7\uffff\1\132\6\uffff\1\153\22\uffff\1\130\4\uffff\1\131",
            "",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\144\1\143\1\140\1\uffff\1\150\1\141\1\uffff\1\147\1\137\1\142\1\151\4\uffff\1\135\1\152\1\uffff\1\146\1\uffff\1\136\1\uffff\1\145\3\uffff\1\134\1\uffff\1\133\31\uffff\1\132\31\uffff\1\130\4\uffff\1\131",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102",
            "\1\171\1\170\1\165\1\uffff\1\175\1\166\1\uffff\1\174\1\164\1\167\1\176\4\uffff\1\162\1\177\1\uffff\1\173\1\uffff\1\163\1\uffff\1\172\3\uffff\1\161\1\uffff\1\160\31\uffff\1\157\31\uffff\1\155\4\uffff\1\156",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154"
    };

    static final short[] dfa_44 = DFA.unpackEncodedString(dfa_44s);
    static final short[] dfa_45 = DFA.unpackEncodedString(dfa_45s);
    static final char[] dfa_46 = DFA.unpackEncodedStringToUnsignedChars(dfa_46s);
    static final char[] dfa_47 = DFA.unpackEncodedStringToUnsignedChars(dfa_47s);
    static final short[] dfa_48 = DFA.unpackEncodedString(dfa_48s);
    static final short[] dfa_49 = DFA.unpackEncodedString(dfa_49s);
    static final short[][] dfa_50 = unpackEncodedStringArray(dfa_50s);

    class DFA63 extends DFA {

        public DFA63(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 63;
            this.eot = dfa_44;
            this.eof = dfa_45;
            this.min = dfa_46;
            this.max = dfa_47;
            this.accept = dfa_48;
            this.special = dfa_49;
            this.transition = dfa_50;
        }
        public String getDescription() {
            return "2441:2: ( ( ( ( ruleQualifiedName ) ) otherlv_1= LeftParenthesis ( ( (lv_arguments_2_0= ruleAssertionArgument ) ) (otherlv_3= Comma ( (lv_arguments_4_0= ruleAssertionArgument ) ) )* )? otherlv_5= RightParenthesis otherlv_6= Colon ( (lv_value_7_0= ruleExpr ) ) ) | ( ( (lv_value_8_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_10= LeftParenthesis ( ( (lv_arguments_11_0= ruleAssertionArgument ) ) (otherlv_12= Comma ( (lv_arguments_13_0= ruleAssertionArgument ) ) )* )? otherlv_14= RightParenthesis ) )";
        }
    }
    static final String dfa_51s = "\61\uffff";
    static final String dfa_52s = "\4\uffff\23\34\7\uffff\23\34";
    static final String dfa_53s = "\1\4\2\uffff\1\4\23\46\3\uffff\1\4\3\uffff\23\46";
    static final String dfa_54s = "\1\131\2\uffff\1\131\23\123\3\uffff\1\131\3\uffff\23\123";
    static final String dfa_55s = "\1\uffff\1\1\1\2\24\uffff\1\4\1\7\1\10\1\uffff\1\3\1\6\1\5\23\uffff";
    static final String dfa_56s = "\61\uffff}>";
    static final String[] dfa_57s = {
            "\1\20\1\17\1\14\1\27\1\24\1\15\1\uffff\1\23\1\13\1\16\1\25\3\uffff\1\27\1\11\1\26\1\30\1\22\1\uffff\1\12\1\uffff\1\21\1\uffff\2\30\1\10\1\uffff\1\7\1\uffff\1\27\2\uffff\1\30\4\uffff\1\27\7\uffff\1\3\7\uffff\1\6\2\uffff\1\2\1\uffff\1\31\1\uffff\1\30\1\1\1\uffff\1\1\17\uffff\1\4\2\30\1\uffff\1\30\1\5",
            "",
            "",
            "\1\20\1\17\1\14\1\uffff\1\24\1\15\1\uffff\1\23\1\13\1\16\1\25\4\uffff\1\11\1\26\1\uffff\1\22\1\uffff\1\12\1\uffff\1\21\3\uffff\1\10\1\uffff\1\7\31\uffff\1\6\31\uffff\1\4\4\uffff\1\5",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "",
            "",
            "",
            "\1\52\1\51\1\46\1\uffff\1\56\1\47\1\uffff\1\55\1\45\1\50\1\57\4\uffff\1\43\1\60\1\uffff\1\54\1\uffff\1\44\1\uffff\1\53\3\uffff\1\42\1\uffff\1\41\31\uffff\1\40\31\uffff\1\36\4\uffff\1\37",
            "",
            "",
            "",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32",
            "\1\34\1\uffff\2\34\1\uffff\3\34\1\uffff\3\34\1\uffff\7\34\1\uffff\2\34\2\uffff\1\35\7\34\1\uffff\2\34\1\uffff\1\34\4\uffff\1\33\1\34\1\35\1\32"
    };

    static final short[] dfa_51 = DFA.unpackEncodedString(dfa_51s);
    static final short[] dfa_52 = DFA.unpackEncodedString(dfa_52s);
    static final char[] dfa_53 = DFA.unpackEncodedStringToUnsignedChars(dfa_53s);
    static final char[] dfa_54 = DFA.unpackEncodedStringToUnsignedChars(dfa_54s);
    static final short[] dfa_55 = DFA.unpackEncodedString(dfa_55s);
    static final short[] dfa_56 = DFA.unpackEncodedString(dfa_56s);
    static final short[][] dfa_57 = unpackEncodedStringArray(dfa_57s);

    class DFA72 extends DFA {

        public DFA72(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 72;
            this.eot = dfa_51;
            this.eof = dfa_52;
            this.min = dfa_53;
            this.max = dfa_54;
            this.accept = dfa_55;
            this.special = dfa_56;
            this.transition = dfa_57;
        }
        public String getDescription() {
            return "3326:2: (this_ArithmeticUnaryExpr_0= ruleArithmeticUnaryExpr | this_NegationExpr_1= ruleNegationExpr | this_AggregationExpr_2= ruleAggregationExpr | this_ModalExpr_3= ruleModalExpr | this_Atom_4= ruleAtom | this_VariableOrNodeExpr_5= ruleVariableOrNodeExpr | this_Constant_6= ruleConstant | (otherlv_7= LeftParenthesis this_Expr_8= ruleExpr otherlv_9= RightParenthesis ) )";
        }
    }
    static final String dfa_58s = "\2\4\23\77\1\uffff\2\4\23\77\1\4\24\100\1\105\2\4\1\uffff\23\100\1\4\24\100\1\4\23\100";
    static final String dfa_59s = "\2\131\23\123\1\uffff\2\131\23\123\1\131\23\123\1\103\1\107\2\131\1\uffff\23\123\1\131\23\123\1\103\1\131\23\123";
    static final String[] dfa_60s = {
            "\1\16\1\15\1\12\1\uffff\1\22\1\13\1\uffff\1\21\1\11\1\14\1\23\4\uffff\1\7\1\24\1\uffff\1\20\1\uffff\1\10\1\uffff\1\17\3\uffff\1\6\1\uffff\1\5\21\uffff\1\1\7\uffff\1\4\2\uffff\1\25\16\uffff\1\25\7\uffff\1\2\4\uffff\1\3",
            "\1\16\1\15\1\12\1\uffff\1\22\1\13\1\uffff\1\21\1\11\1\14\1\23\4\uffff\1\7\1\24\1\uffff\1\20\1\uffff\1\10\1\uffff\1\17\3\uffff\1\6\1\uffff\1\5\31\uffff\1\4\31\uffff\1\2\4\uffff\1\3",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "",
            "\1\44\1\43\1\40\1\uffff\1\50\1\41\1\uffff\1\47\1\37\1\42\1\51\4\uffff\1\35\1\52\1\uffff\1\46\1\uffff\1\36\1\uffff\1\45\3\uffff\1\34\1\uffff\1\33\31\uffff\1\32\31\uffff\1\30\4\uffff\1\31",
            "\1\70\1\67\1\64\1\uffff\1\74\1\65\1\uffff\1\73\1\63\1\66\1\75\4\uffff\1\61\1\76\1\uffff\1\72\1\uffff\1\62\1\uffff\1\71\3\uffff\1\60\1\uffff\1\57\21\uffff\1\53\7\uffff\1\56\5\uffff\1\100\1\77\22\uffff\1\54\4\uffff\1\55",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\27\23\uffff\1\26",
            "\1\70\1\67\1\64\1\uffff\1\74\1\65\1\uffff\1\73\1\63\1\66\1\75\4\uffff\1\61\1\76\1\uffff\1\72\1\uffff\1\62\1\uffff\1\71\3\uffff\1\60\1\uffff\1\57\31\uffff\1\56\31\uffff\1\54\4\uffff\1\55",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102",
            "\1\25\1\uffff\1\103",
            "\1\120\1\117\1\114\1\uffff\1\124\1\115\1\uffff\1\123\1\113\1\116\1\125\4\uffff\1\111\1\126\1\uffff\1\122\1\uffff\1\112\1\uffff\1\121\3\uffff\1\110\1\uffff\1\107\31\uffff\1\106\31\uffff\1\104\4\uffff\1\105",
            "\1\144\1\143\1\140\1\uffff\1\150\1\141\1\uffff\1\147\1\137\1\142\1\151\4\uffff\1\135\1\152\1\uffff\1\146\1\uffff\1\136\1\uffff\1\145\3\uffff\1\134\1\uffff\1\133\21\uffff\1\127\7\uffff\1\132\6\uffff\1\153\22\uffff\1\130\4\uffff\1\131",
            "",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\100\2\uffff\1\102\17\uffff\1\101",
            "\1\144\1\143\1\140\1\uffff\1\150\1\141\1\uffff\1\147\1\137\1\142\1\151\4\uffff\1\135\1\152\1\uffff\1\146\1\uffff\1\136\1\uffff\1\145\3\uffff\1\134\1\uffff\1\133\31\uffff\1\132\31\uffff\1\130\4\uffff\1\131",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102",
            "\1\171\1\170\1\165\1\uffff\1\175\1\166\1\uffff\1\174\1\164\1\167\1\176\4\uffff\1\162\1\177\1\uffff\1\173\1\uffff\1\163\1\uffff\1\172\3\uffff\1\161\1\uffff\1\160\31\uffff\1\157\31\uffff\1\155\4\uffff\1\156",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154",
            "\1\100\2\uffff\1\102\17\uffff\1\154"
    };
    static final char[] dfa_58 = DFA.unpackEncodedStringToUnsignedChars(dfa_58s);
    static final char[] dfa_59 = DFA.unpackEncodedStringToUnsignedChars(dfa_59s);
    static final short[][] dfa_60 = unpackEncodedStringArray(dfa_60s);

    class DFA86 extends DFA {

        public DFA86(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 86;
            this.eot = dfa_44;
            this.eof = dfa_44;
            this.min = dfa_58;
            this.max = dfa_59;
            this.accept = dfa_48;
            this.special = dfa_49;
            this.transition = dfa_60;
        }
        public String getDescription() {
            return "4132:3: ( ( ( ( ruleQualifiedName ) ) otherlv_2= LeftParenthesis ( ( (lv_arguments_3_0= ruleAssertionArgument ) ) (otherlv_4= Comma ( (lv_arguments_5_0= ruleAssertionArgument ) ) )* )? otherlv_6= RightParenthesis otherlv_7= Colon ( (lv_value_8_0= ruleExpr ) ) ) | ( ( (lv_value_9_0= ruleShortLogicConstant ) ) ( ( ruleQualifiedName ) ) otherlv_11= LeftParenthesis ( ( (lv_arguments_12_0= ruleAssertionArgument ) ) (otherlv_13= Comma ( (lv_arguments_14_0= ruleAssertionArgument ) ) )* )? otherlv_15= RightParenthesis ) )";
        }
    }
 

    public static final BitSet FOLLOW_1 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_2 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_3 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002100020L});
    public static final BitSet FOLLOW_4 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_5 = new BitSet(new long[]{0x6404001BDDD9FF72L,0x0000000002103000L});
    public static final BitSet FOLLOW_6 = new BitSet(new long[]{0x4404001B5D58FF70L,0x0000000002102000L});
    public static final BitSet FOLLOW_7 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_8 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002100000L});
    public static final BitSet FOLLOW_9 = new BitSet(new long[]{0x0000000000020000L,0x0000000000010020L});
    public static final BitSet FOLLOW_10 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010028L});
    public static final BitSet FOLLOW_11 = new BitSet(new long[]{0x0404000147483B70L,0x0000000002122000L});
    public static final BitSet FOLLOW_12 = new BitSet(new long[]{0x0404000147483B70L,0x0000000002122100L});
    public static final BitSet FOLLOW_13 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010020L});
    public static final BitSet FOLLOW_14 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002122000L});
    public static final BitSet FOLLOW_15 = new BitSet(new long[]{0x0000000000000000L,0x0000000000020108L});
    public static final BitSet FOLLOW_16 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002102000L});
    public static final BitSet FOLLOW_17 = new BitSet(new long[]{0x0000000000000000L,0x0000000000020000L});
    public static final BitSet FOLLOW_18 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_19 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_20 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_21 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_22 = new BitSet(new long[]{0x0404000945587B70L,0x0000000002102001L});
    public static final BitSet FOLLOW_23 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000009L});
    public static final BitSet FOLLOW_24 = new BitSet(new long[]{0x0404000945587B70L,0x0000000002102000L});
    public static final BitSet FOLLOW_25 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_26 = new BitSet(new long[]{0x0000008000100000L,0x0000000000000020L});
    public static final BitSet FOLLOW_27 = new BitSet(new long[]{0x0000008000000000L,0x0000000000000028L});
    public static final BitSet FOLLOW_28 = new BitSet(new long[]{0xA4040425757C7BF0L,0x0000000003700016L});
    public static final BitSet FOLLOW_29 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000120L});
    public static final BitSet FOLLOW_30 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000420L});
    public static final BitSet FOLLOW_31 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_32 = new BitSet(new long[]{0x0000028000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_33 = new BitSet(new long[]{0x0000020000000000L,0x0000000000000120L});
    public static final BitSet FOLLOW_34 = new BitSet(new long[]{0x2404000145587B70L,0x0000000002101000L});
    public static final BitSet FOLLOW_35 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000028L});
    public static final BitSet FOLLOW_36 = new BitSet(new long[]{0x0000000000000002L,0x0000000000002000L});
    public static final BitSet FOLLOW_37 = new BitSet(new long[]{0x8000000000000002L});
    public static final BitSet FOLLOW_38 = new BitSet(new long[]{0xA4040425757C7BF0L,0x0000000003700017L});
    public static final BitSet FOLLOW_39 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_40 = new BitSet(new long[]{0x0400000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_41 = new BitSet(new long[]{0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_42 = new BitSet(new long[]{0x0404000147483B70L,0x0000000002102000L});
    public static final BitSet FOLLOW_43 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002104000L});
    public static final BitSet FOLLOW_44 = new BitSet(new long[]{0x0000000000104002L});
    public static final BitSet FOLLOW_45 = new BitSet(new long[]{0x0000000000104002L,0x0000000000000008L});
    public static final BitSet FOLLOW_46 = new BitSet(new long[]{0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_47 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_48 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000008L});
    public static final BitSet FOLLOW_49 = new BitSet(new long[]{0x0000800000000002L});
    public static final BitSet FOLLOW_50 = new BitSet(new long[]{0x0404000945587B70L,0x0000000002100000L});
    public static final BitSet FOLLOW_51 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002100003L});
    public static final BitSet FOLLOW_52 = new BitSet(new long[]{0x0404000145587B70L,0x0000000002100002L});
    public static final BitSet FOLLOW_53 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
    public static final BitSet FOLLOW_54 = new BitSet(new long[]{0x0800000000000002L});
    public static final BitSet FOLLOW_55 = new BitSet(new long[]{0x1200100000000002L});
    public static final BitSet FOLLOW_56 = new BitSet(new long[]{0x00F8094000000002L,0x0000000000000A00L});
    public static final BitSet FOLLOW_57 = new BitSet(new long[]{0x0102000000000002L});
    public static final BitSet FOLLOW_58 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000014L});
    public static final BitSet FOLLOW_59 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000042L});
    public static final BitSet FOLLOW_60 = new BitSet(new long[]{0x0000200000000002L});
    public static final BitSet FOLLOW_61 = new BitSet(new long[]{0x0001000000000002L});
    public static final BitSet FOLLOW_62 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_63 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_64 = new BitSet(new long[]{0x0000800000000000L,0x0000000000020000L});
    public static final BitSet FOLLOW_65 = new BitSet(new long[]{0x8000000000000000L,0x0000000000040000L});
    public static final BitSet FOLLOW_66 = new BitSet(new long[]{0x0000400000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_67 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_68 = new BitSet(new long[]{0x0000000000000000L,0x0000000000200002L});
    public static final BitSet FOLLOW_69 = new BitSet(new long[]{0x0000000000000002L,0x0000000000080000L});
    public static final BitSet FOLLOW_70 = new BitSet(new long[]{0x0000000000000000L,0x0000000000600000L});

}
