package tools.refinery.language.parser.antlr.lexer;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.parser.antlr.Lexer;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class InternalProblemLexer extends Lexer {
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

    public InternalProblemLexer() {;} 
    public InternalProblemLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public InternalProblemLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "InternalProblemLexer.g"; }

    // $ANTLR start "Concretization"
    public final void mConcretization() throws RecognitionException {
        try {
            int _type = Concretization;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:14:16: ( 'concretization' )
            // InternalProblemLexer.g:14:18: 'concretization'
            {
            match("concretization"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Concretization"

    // $ANTLR start "Propagation"
    public final void mPropagation() throws RecognitionException {
        try {
            int _type = Propagation;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:16:13: ( 'propagation' )
            // InternalProblemLexer.g:16:15: 'propagation'
            {
            match("propagation"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Propagation"

    // $ANTLR start "Aggregator"
    public final void mAggregator() throws RecognitionException {
        try {
            int _type = Aggregator;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:18:12: ( 'aggregator' )
            // InternalProblemLexer.g:18:14: 'aggregator'
            {
            match("aggregator"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Aggregator"

    // $ANTLR start "Candidate"
    public final void mCandidate() throws RecognitionException {
        try {
            int _type = Candidate;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:20:11: ( 'candidate' )
            // InternalProblemLexer.g:20:13: 'candidate'
            {
            match("candidate"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Candidate"

    // $ANTLR start "Container"
    public final void mContainer() throws RecognitionException {
        try {
            int _type = Container;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:22:11: ( 'container' )
            // InternalProblemLexer.g:22:13: 'container'
            {
            match("container"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Container"

    // $ANTLR start "Primitive"
    public final void mPrimitive() throws RecognitionException {
        try {
            int _type = Primitive;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:24:11: ( 'primitive' )
            // InternalProblemLexer.g:24:13: 'primitive'
            {
            match("primitive"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Primitive"

    // $ANTLR start "Abstract"
    public final void mAbstract() throws RecognitionException {
        try {
            int _type = Abstract;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:26:10: ( 'abstract' )
            // InternalProblemLexer.g:26:12: 'abstract'
            {
            match("abstract"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Abstract"

    // $ANTLR start "Contains"
    public final void mContains() throws RecognitionException {
        try {
            int _type = Contains;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:28:10: ( 'contains' )
            // InternalProblemLexer.g:28:12: 'contains'
            {
            match("contains"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Contains"

    // $ANTLR start "Datatype"
    public final void mDatatype() throws RecognitionException {
        try {
            int _type = Datatype;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:30:10: ( 'datatype' )
            // InternalProblemLexer.g:30:12: 'datatype'
            {
            match("datatype"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Datatype"

    // $ANTLR start "Decision"
    public final void mDecision() throws RecognitionException {
        try {
            int _type = Decision;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:32:10: ( 'decision' )
            // InternalProblemLexer.g:32:12: 'decision'
            {
            match("decision"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Decision"

    // $ANTLR start "Opposite"
    public final void mOpposite() throws RecognitionException {
        try {
            int _type = Opposite;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:34:10: ( 'opposite' )
            // InternalProblemLexer.g:34:12: 'opposite'
            {
            match("opposite"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Opposite"

    // $ANTLR start "Declare"
    public final void mDeclare() throws RecognitionException {
        try {
            int _type = Declare;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:36:9: ( 'declare' )
            // InternalProblemLexer.g:36:11: 'declare'
            {
            match("declare"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Declare"

    // $ANTLR start "Default"
    public final void mDefault() throws RecognitionException {
        try {
            int _type = Default;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:38:9: ( 'default' )
            // InternalProblemLexer.g:38:11: 'default'
            {
            match("default"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Default"

    // $ANTLR start "Extends"
    public final void mExtends() throws RecognitionException {
        try {
            int _type = Extends;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:40:9: ( 'extends' )
            // InternalProblemLexer.g:40:11: 'extends'
            {
            match("extends"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Extends"

    // $ANTLR start "Partial"
    public final void mPartial() throws RecognitionException {
        try {
            int _type = Partial;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:42:9: ( 'partial' )
            // InternalProblemLexer.g:42:11: 'partial'
            {
            match("partial"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Partial"

    // $ANTLR start "Problem"
    public final void mProblem() throws RecognitionException {
        try {
            int _type = Problem;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:44:9: ( 'problem' )
            // InternalProblemLexer.g:44:11: 'problem'
            {
            match("problem"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Problem"

    // $ANTLR start "Subsets"
    public final void mSubsets() throws RecognitionException {
        try {
            int _type = Subsets;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:46:9: ( 'subsets' )
            // InternalProblemLexer.g:46:11: 'subsets'
            {
            match("subsets"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Subsets"

    // $ANTLR start "Unknown"
    public final void mUnknown() throws RecognitionException {
        try {
            int _type = Unknown;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:48:9: ( 'unknown' )
            // InternalProblemLexer.g:48:11: 'unknown'
            {
            match("unknown"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Unknown"

    // $ANTLR start "Assert"
    public final void mAssert() throws RecognitionException {
        try {
            int _type = Assert;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:50:8: ( 'assert' )
            // InternalProblemLexer.g:50:10: 'assert'
            {
            match("assert"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Assert"

    // $ANTLR start "Import"
    public final void mImport() throws RecognitionException {
        try {
            int _type = Import;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:52:8: ( 'import' )
            // InternalProblemLexer.g:52:10: 'import'
            {
            match("import"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Import"

    // $ANTLR start "Module"
    public final void mModule() throws RecognitionException {
        try {
            int _type = Module;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:54:8: ( 'module' )
            // InternalProblemLexer.g:54:10: 'module'
            {
            match("module"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Module"

    // $ANTLR start "Refers"
    public final void mRefers() throws RecognitionException {
        try {
            int _type = Refers;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:56:8: ( 'refers' )
            // InternalProblemLexer.g:56:10: 'refers'
            {
            match("refers"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Refers"

    // $ANTLR start "Shadow"
    public final void mShadow() throws RecognitionException {
        try {
            int _type = Shadow;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:58:8: ( 'shadow' )
            // InternalProblemLexer.g:58:10: 'shadow'
            {
            match("shadow"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Shadow"

    // $ANTLR start "Class"
    public final void mClass() throws RecognitionException {
        try {
            int _type = Class;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:60:7: ( 'class' )
            // InternalProblemLexer.g:60:9: 'class'
            {
            match("class"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Class"

    // $ANTLR start "Error"
    public final void mError() throws RecognitionException {
        try {
            int _type = Error;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:62:7: ( 'error' )
            // InternalProblemLexer.g:62:9: 'error'
            {
            match("error"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Error"

    // $ANTLR start "False"
    public final void mFalse() throws RecognitionException {
        try {
            int _type = False;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:64:7: ( 'false' )
            // InternalProblemLexer.g:64:9: 'false'
            {
            match("false"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "False"

    // $ANTLR start "Multi"
    public final void mMulti() throws RecognitionException {
        try {
            int _type = Multi;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:66:7: ( 'multi' )
            // InternalProblemLexer.g:66:9: 'multi'
            {
            match("multi"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Multi"

    // $ANTLR start "Scope"
    public final void mScope() throws RecognitionException {
        try {
            int _type = Scope;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:68:7: ( 'scope' )
            // InternalProblemLexer.g:68:9: 'scope'
            {
            match("scope"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Scope"

    // $ANTLR start "Atom"
    public final void mAtom() throws RecognitionException {
        try {
            int _type = Atom;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:70:6: ( 'atom' )
            // InternalProblemLexer.g:70:8: 'atom'
            {
            match("atom"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Atom"

    // $ANTLR start "Enum"
    public final void mEnum() throws RecognitionException {
        try {
            int _type = Enum;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:72:6: ( 'enum' )
            // InternalProblemLexer.g:72:8: 'enum'
            {
            match("enum"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Enum"

    // $ANTLR start "Must"
    public final void mMust() throws RecognitionException {
        try {
            int _type = Must;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:74:6: ( 'must' )
            // InternalProblemLexer.g:74:8: 'must'
            {
            match("must"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Must"

    // $ANTLR start "Pred"
    public final void mPred() throws RecognitionException {
        try {
            int _type = Pred;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:76:6: ( 'pred' )
            // InternalProblemLexer.g:76:8: 'pred'
            {
            match("pred"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Pred"

    // $ANTLR start "Rule"
    public final void mRule() throws RecognitionException {
        try {
            int _type = Rule;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:78:6: ( 'rule' )
            // InternalProblemLexer.g:78:8: 'rule'
            {
            match("rule"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Rule"

    // $ANTLR start "True"
    public final void mTrue() throws RecognitionException {
        try {
            int _type = True;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:80:6: ( 'true' )
            // InternalProblemLexer.g:80:8: 'true'
            {
            match("true"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "True"

    // $ANTLR start "ExclamationMarkEqualsSignEqualsSign"
    public final void mExclamationMarkEqualsSignEqualsSign() throws RecognitionException {
        try {
            int _type = ExclamationMarkEqualsSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:82:37: ( '!==' )
            // InternalProblemLexer.g:82:39: '!=='
            {
            match("!=="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ExclamationMarkEqualsSignEqualsSign"

    // $ANTLR start "LessThanSignHyphenMinusGreaterThanSign"
    public final void mLessThanSignHyphenMinusGreaterThanSign() throws RecognitionException {
        try {
            int _type = LessThanSignHyphenMinusGreaterThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:84:40: ( '<->' )
            // InternalProblemLexer.g:84:42: '<->'
            {
            match("<->"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LessThanSignHyphenMinusGreaterThanSign"

    // $ANTLR start "EqualsSignEqualsSignEqualsSign"
    public final void mEqualsSignEqualsSignEqualsSign() throws RecognitionException {
        try {
            int _type = EqualsSignEqualsSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:86:32: ( '===' )
            // InternalProblemLexer.g:86:34: '==='
            {
            match("==="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EqualsSignEqualsSignEqualsSign"

    // $ANTLR start "EqualsSignEqualsSignGreaterThanSign"
    public final void mEqualsSignEqualsSignGreaterThanSign() throws RecognitionException {
        try {
            int _type = EqualsSignEqualsSignGreaterThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:88:37: ( '==>' )
            // InternalProblemLexer.g:88:39: '==>'
            {
            match("==>"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EqualsSignEqualsSignGreaterThanSign"

    // $ANTLR start "May"
    public final void mMay() throws RecognitionException {
        try {
            int _type = May;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:90:5: ( 'may' )
            // InternalProblemLexer.g:90:7: 'may'
            {
            match("may"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "May"

    // $ANTLR start "ExclamationMarkEqualsSign"
    public final void mExclamationMarkEqualsSign() throws RecognitionException {
        try {
            int _type = ExclamationMarkEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:92:27: ( '!=' )
            // InternalProblemLexer.g:92:29: '!='
            {
            match("!="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ExclamationMarkEqualsSign"

    // $ANTLR start "AmpersandAmpersand"
    public final void mAmpersandAmpersand() throws RecognitionException {
        try {
            int _type = AmpersandAmpersand;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:94:20: ( '&&' )
            // InternalProblemLexer.g:94:22: '&&'
            {
            match("&&"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AmpersandAmpersand"

    // $ANTLR start "AsteriskAsterisk"
    public final void mAsteriskAsterisk() throws RecognitionException {
        try {
            int _type = AsteriskAsterisk;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:96:18: ( '**' )
            // InternalProblemLexer.g:96:20: '**'
            {
            match("**"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AsteriskAsterisk"

    // $ANTLR start "PlusSignEqualsSign"
    public final void mPlusSignEqualsSign() throws RecognitionException {
        try {
            int _type = PlusSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:98:20: ( '+=' )
            // InternalProblemLexer.g:98:22: '+='
            {
            match("+="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "PlusSignEqualsSign"

    // $ANTLR start "HyphenMinusGreaterThanSign"
    public final void mHyphenMinusGreaterThanSign() throws RecognitionException {
        try {
            int _type = HyphenMinusGreaterThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:100:28: ( '->' )
            // InternalProblemLexer.g:100:30: '->'
            {
            match("->"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "HyphenMinusGreaterThanSign"

    // $ANTLR start "FullStopFullStop"
    public final void mFullStopFullStop() throws RecognitionException {
        try {
            int _type = FullStopFullStop;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:102:18: ( '..' )
            // InternalProblemLexer.g:102:20: '..'
            {
            match(".."); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "FullStopFullStop"

    // $ANTLR start "SolidusReverseSolidus"
    public final void mSolidusReverseSolidus() throws RecognitionException {
        try {
            int _type = SolidusReverseSolidus;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:104:23: ( '/\\\\' )
            // InternalProblemLexer.g:104:25: '/\\\\'
            {
            match("/\\"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SolidusReverseSolidus"

    // $ANTLR start "ColonColon"
    public final void mColonColon() throws RecognitionException {
        try {
            int _type = ColonColon;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:106:12: ( '::' )
            // InternalProblemLexer.g:106:14: '::'
            {
            match("::"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ColonColon"

    // $ANTLR start "ColonGreaterThanSign"
    public final void mColonGreaterThanSign() throws RecognitionException {
        try {
            int _type = ColonGreaterThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:108:22: ( ':>' )
            // InternalProblemLexer.g:108:24: ':>'
            {
            match(":>"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ColonGreaterThanSign"

    // $ANTLR start "LessThanSignColon"
    public final void mLessThanSignColon() throws RecognitionException {
        try {
            int _type = LessThanSignColon;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:110:19: ( '<:' )
            // InternalProblemLexer.g:110:21: '<:'
            {
            match("<:"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LessThanSignColon"

    // $ANTLR start "LessThanSignEqualsSign"
    public final void mLessThanSignEqualsSign() throws RecognitionException {
        try {
            int _type = LessThanSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:112:24: ( '<=' )
            // InternalProblemLexer.g:112:26: '<='
            {
            match("<="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LessThanSignEqualsSign"

    // $ANTLR start "EqualsSignEqualsSign"
    public final void mEqualsSignEqualsSign() throws RecognitionException {
        try {
            int _type = EqualsSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:114:22: ( '==' )
            // InternalProblemLexer.g:114:24: '=='
            {
            match("=="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EqualsSignEqualsSign"

    // $ANTLR start "GreaterThanSignEqualsSign"
    public final void mGreaterThanSignEqualsSign() throws RecognitionException {
        try {
            int _type = GreaterThanSignEqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:116:27: ( '>=' )
            // InternalProblemLexer.g:116:29: '>='
            {
            match(">="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "GreaterThanSignEqualsSign"

    // $ANTLR start "ReverseSolidusSolidus"
    public final void mReverseSolidusSolidus() throws RecognitionException {
        try {
            int _type = ReverseSolidusSolidus;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:118:23: ( '\\\\/' )
            // InternalProblemLexer.g:118:25: '\\\\/'
            {
            match("\\/"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ReverseSolidusSolidus"

    // $ANTLR start "CircumflexAccentCircumflexAccent"
    public final void mCircumflexAccentCircumflexAccent() throws RecognitionException {
        try {
            int _type = CircumflexAccentCircumflexAccent;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:120:34: ( '^^' )
            // InternalProblemLexer.g:120:36: '^^'
            {
            match("^^"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "CircumflexAccentCircumflexAccent"

    // $ANTLR start "As"
    public final void mAs() throws RecognitionException {
        try {
            int _type = As;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:122:4: ( 'as' )
            // InternalProblemLexer.g:122:6: 'as'
            {
            match("as"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "As"

    // $ANTLR start "Is"
    public final void mIs() throws RecognitionException {
        try {
            int _type = Is;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:124:4: ( 'is' )
            // InternalProblemLexer.g:124:6: 'is'
            {
            match("is"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Is"

    // $ANTLR start "VerticalLineVerticalLine"
    public final void mVerticalLineVerticalLine() throws RecognitionException {
        try {
            int _type = VerticalLineVerticalLine;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:126:26: ( '||' )
            // InternalProblemLexer.g:126:28: '||'
            {
            match("||"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "VerticalLineVerticalLine"

    // $ANTLR start "ExclamationMark"
    public final void mExclamationMark() throws RecognitionException {
        try {
            int _type = ExclamationMark;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:128:17: ( '!' )
            // InternalProblemLexer.g:128:19: '!'
            {
            match('!'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ExclamationMark"

    // $ANTLR start "NumberSign"
    public final void mNumberSign() throws RecognitionException {
        try {
            int _type = NumberSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:130:12: ( '#' )
            // InternalProblemLexer.g:130:14: '#'
            {
            match('#'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NumberSign"

    // $ANTLR start "LeftParenthesis"
    public final void mLeftParenthesis() throws RecognitionException {
        try {
            int _type = LeftParenthesis;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:132:17: ( '(' )
            // InternalProblemLexer.g:132:19: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LeftParenthesis"

    // $ANTLR start "RightParenthesis"
    public final void mRightParenthesis() throws RecognitionException {
        try {
            int _type = RightParenthesis;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:134:18: ( ')' )
            // InternalProblemLexer.g:134:20: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RightParenthesis"

    // $ANTLR start "Asterisk"
    public final void mAsterisk() throws RecognitionException {
        try {
            int _type = Asterisk;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:136:10: ( '*' )
            // InternalProblemLexer.g:136:12: '*'
            {
            match('*'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Asterisk"

    // $ANTLR start "PlusSign"
    public final void mPlusSign() throws RecognitionException {
        try {
            int _type = PlusSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:138:10: ( '+' )
            // InternalProblemLexer.g:138:12: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "PlusSign"

    // $ANTLR start "Comma"
    public final void mComma() throws RecognitionException {
        try {
            int _type = Comma;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:140:7: ( ',' )
            // InternalProblemLexer.g:140:9: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Comma"

    // $ANTLR start "HyphenMinus"
    public final void mHyphenMinus() throws RecognitionException {
        try {
            int _type = HyphenMinus;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:142:13: ( '-' )
            // InternalProblemLexer.g:142:15: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "HyphenMinus"

    // $ANTLR start "FullStop"
    public final void mFullStop() throws RecognitionException {
        try {
            int _type = FullStop;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:144:10: ( '.' )
            // InternalProblemLexer.g:144:12: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "FullStop"

    // $ANTLR start "Solidus"
    public final void mSolidus() throws RecognitionException {
        try {
            int _type = Solidus;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:146:9: ( '/' )
            // InternalProblemLexer.g:146:11: '/'
            {
            match('/'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Solidus"

    // $ANTLR start "Colon"
    public final void mColon() throws RecognitionException {
        try {
            int _type = Colon;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:148:7: ( ':' )
            // InternalProblemLexer.g:148:9: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Colon"

    // $ANTLR start "Semicolon"
    public final void mSemicolon() throws RecognitionException {
        try {
            int _type = Semicolon;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:150:11: ( ';' )
            // InternalProblemLexer.g:150:13: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "Semicolon"

    // $ANTLR start "LessThanSign"
    public final void mLessThanSign() throws RecognitionException {
        try {
            int _type = LessThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:152:14: ( '<' )
            // InternalProblemLexer.g:152:16: '<'
            {
            match('<'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LessThanSign"

    // $ANTLR start "EqualsSign"
    public final void mEqualsSign() throws RecognitionException {
        try {
            int _type = EqualsSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:154:12: ( '=' )
            // InternalProblemLexer.g:154:14: '='
            {
            match('='); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EqualsSign"

    // $ANTLR start "GreaterThanSign"
    public final void mGreaterThanSign() throws RecognitionException {
        try {
            int _type = GreaterThanSign;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:156:17: ( '>' )
            // InternalProblemLexer.g:156:19: '>'
            {
            match('>'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "GreaterThanSign"

    // $ANTLR start "QuestionMark"
    public final void mQuestionMark() throws RecognitionException {
        try {
            int _type = QuestionMark;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:158:14: ( '?' )
            // InternalProblemLexer.g:158:16: '?'
            {
            match('?'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "QuestionMark"

    // $ANTLR start "CommercialAt"
    public final void mCommercialAt() throws RecognitionException {
        try {
            int _type = CommercialAt;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:160:14: ( '@' )
            // InternalProblemLexer.g:160:16: '@'
            {
            match('@'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "CommercialAt"

    // $ANTLR start "LeftSquareBracket"
    public final void mLeftSquareBracket() throws RecognitionException {
        try {
            int _type = LeftSquareBracket;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:162:19: ( '[' )
            // InternalProblemLexer.g:162:21: '['
            {
            match('['); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LeftSquareBracket"

    // $ANTLR start "RightSquareBracket"
    public final void mRightSquareBracket() throws RecognitionException {
        try {
            int _type = RightSquareBracket;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:164:20: ( ']' )
            // InternalProblemLexer.g:164:22: ']'
            {
            match(']'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RightSquareBracket"

    // $ANTLR start "LeftCurlyBracket"
    public final void mLeftCurlyBracket() throws RecognitionException {
        try {
            int _type = LeftCurlyBracket;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:166:18: ( '{' )
            // InternalProblemLexer.g:166:20: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LeftCurlyBracket"

    // $ANTLR start "RightCurlyBracket"
    public final void mRightCurlyBracket() throws RecognitionException {
        try {
            int _type = RightCurlyBracket;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:168:19: ( '}' )
            // InternalProblemLexer.g:168:21: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RightCurlyBracket"

    // $ANTLR start "RULE_TRANSITIVE_CLOSURE"
    public final void mRULE_TRANSITIVE_CLOSURE() throws RecognitionException {
        try {
            // InternalProblemLexer.g:170:34: ()
            // InternalProblemLexer.g:170:36: 
            {
            }

        }
        finally {
        }
    }
    // $ANTLR end "RULE_TRANSITIVE_CLOSURE"

    // $ANTLR start "RULE_QUALIFIED_NAME_SEPARATOR"
    public final void mRULE_QUALIFIED_NAME_SEPARATOR() throws RecognitionException {
        try {
            int _type = RULE_QUALIFIED_NAME_SEPARATOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:172:31: ( 'synthetic::QUALIFIED_NAME_SEPARATOR' )
            // InternalProblemLexer.g:172:33: 'synthetic::QUALIFIED_NAME_SEPARATOR'
            {
            match("synthetic::QUALIFIED_NAME_SEPARATOR"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_QUALIFIED_NAME_SEPARATOR"

    // $ANTLR start "RULE_ID"
    public final void mRULE_ID() throws RecognitionException {
        try {
            int _type = RULE_ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:174:9: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )* )
            // InternalProblemLexer.g:174:11: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // InternalProblemLexer.g:174:35: ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( ((LA1_0>='0' && LA1_0<='9')||(LA1_0>='A' && LA1_0<='Z')||LA1_0=='_'||(LA1_0>='a' && LA1_0<='z')) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // InternalProblemLexer.g:
            	    {
            	    if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_ID"

    // $ANTLR start "RULE_EXPONENTIAL"
    public final void mRULE_EXPONENTIAL() throws RecognitionException {
        try {
            int _type = RULE_EXPONENTIAL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:176:18: ( RULE_INT ( 'e' | 'E' ) ( '+' | '-' )? RULE_INT )
            // InternalProblemLexer.g:176:20: RULE_INT ( 'e' | 'E' ) ( '+' | '-' )? RULE_INT
            {
            mRULE_INT(); 
            if ( input.LA(1)=='E'||input.LA(1)=='e' ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // InternalProblemLexer.g:176:39: ( '+' | '-' )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0=='+'||LA2_0=='-') ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // InternalProblemLexer.g:
                    {
                    if ( input.LA(1)=='+'||input.LA(1)=='-' ) {
                        input.consume();

                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;}


                    }
                    break;

            }

            mRULE_INT(); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_EXPONENTIAL"

    // $ANTLR start "RULE_SL_COMMENT"
    public final void mRULE_SL_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_SL_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:178:17: ( ( '%' | '//' ) (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )? )
            // InternalProblemLexer.g:178:19: ( '%' | '//' ) (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )?
            {
            // InternalProblemLexer.g:178:19: ( '%' | '//' )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0=='%') ) {
                alt3=1;
            }
            else if ( (LA3_0=='/') ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // InternalProblemLexer.g:178:20: '%'
                    {
                    match('%'); 

                    }
                    break;
                case 2 :
                    // InternalProblemLexer.g:178:24: '//'
                    {
                    match("//"); 


                    }
                    break;

            }

            // InternalProblemLexer.g:178:30: (~ ( ( '\\n' | '\\r' ) ) )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='\u0000' && LA4_0<='\t')||(LA4_0>='\u000B' && LA4_0<='\f')||(LA4_0>='\u000E' && LA4_0<='\uFFFF')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // InternalProblemLexer.g:178:30: ~ ( ( '\\n' | '\\r' ) )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\f')||(input.LA(1)>='\u000E' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);

            // InternalProblemLexer.g:178:46: ( ( '\\r' )? '\\n' )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0=='\n'||LA6_0=='\r') ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // InternalProblemLexer.g:178:47: ( '\\r' )? '\\n'
                    {
                    // InternalProblemLexer.g:178:47: ( '\\r' )?
                    int alt5=2;
                    int LA5_0 = input.LA(1);

                    if ( (LA5_0=='\r') ) {
                        alt5=1;
                    }
                    switch (alt5) {
                        case 1 :
                            // InternalProblemLexer.g:178:47: '\\r'
                            {
                            match('\r'); 

                            }
                            break;

                    }

                    match('\n'); 

                    }
                    break;

            }


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_SL_COMMENT"

    // $ANTLR start "RULE_STRING"
    public final void mRULE_STRING() throws RecognitionException {
        try {
            int _type = RULE_STRING;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:180:13: ( '\"' ( '\\\\' . | ~ ( ( '\\\\' | '\"' ) ) )* '\"' )
            // InternalProblemLexer.g:180:15: '\"' ( '\\\\' . | ~ ( ( '\\\\' | '\"' ) ) )* '\"'
            {
            match('\"'); 
            // InternalProblemLexer.g:180:19: ( '\\\\' . | ~ ( ( '\\\\' | '\"' ) ) )*
            loop7:
            do {
                int alt7=3;
                int LA7_0 = input.LA(1);

                if ( (LA7_0=='\\') ) {
                    alt7=1;
                }
                else if ( ((LA7_0>='\u0000' && LA7_0<='!')||(LA7_0>='#' && LA7_0<='[')||(LA7_0>=']' && LA7_0<='\uFFFF')) ) {
                    alt7=2;
                }


                switch (alt7) {
            	case 1 :
            	    // InternalProblemLexer.g:180:20: '\\\\' .
            	    {
            	    match('\\'); 
            	    matchAny(); 

            	    }
            	    break;
            	case 2 :
            	    // InternalProblemLexer.g:180:27: ~ ( ( '\\\\' | '\"' ) )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='!')||(input.LA(1)>='#' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);

            match('\"'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_STRING"

    // $ANTLR start "RULE_QUOTED_ID"
    public final void mRULE_QUOTED_ID() throws RecognitionException {
        try {
            int _type = RULE_QUOTED_ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:182:16: ( '\\'' ( '\\\\' . | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )
            // InternalProblemLexer.g:182:18: '\\'' ( '\\\\' . | ~ ( ( '\\\\' | '\\'' ) ) )* '\\''
            {
            match('\''); 
            // InternalProblemLexer.g:182:23: ( '\\\\' . | ~ ( ( '\\\\' | '\\'' ) ) )*
            loop8:
            do {
                int alt8=3;
                int LA8_0 = input.LA(1);

                if ( (LA8_0=='\\') ) {
                    alt8=1;
                }
                else if ( ((LA8_0>='\u0000' && LA8_0<='&')||(LA8_0>='(' && LA8_0<='[')||(LA8_0>=']' && LA8_0<='\uFFFF')) ) {
                    alt8=2;
                }


                switch (alt8) {
            	case 1 :
            	    // InternalProblemLexer.g:182:24: '\\\\' .
            	    {
            	    match('\\'); 
            	    matchAny(); 

            	    }
            	    break;
            	case 2 :
            	    // InternalProblemLexer.g:182:31: ~ ( ( '\\\\' | '\\'' ) )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='&')||(input.LA(1)>='(' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop8;
                }
            } while (true);

            match('\''); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_QUOTED_ID"

    // $ANTLR start "RULE_INT"
    public final void mRULE_INT() throws RecognitionException {
        try {
            int _type = RULE_INT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:184:10: ( ( '0' .. '9' )+ )
            // InternalProblemLexer.g:184:12: ( '0' .. '9' )+
            {
            // InternalProblemLexer.g:184:12: ( '0' .. '9' )+
            int cnt9=0;
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( ((LA9_0>='0' && LA9_0<='9')) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // InternalProblemLexer.g:184:13: '0' .. '9'
            	    {
            	    matchRange('0','9'); 

            	    }
            	    break;

            	default :
            	    if ( cnt9 >= 1 ) break loop9;
                        EarlyExitException eee =
                            new EarlyExitException(9, input);
                        throw eee;
                }
                cnt9++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_INT"

    // $ANTLR start "RULE_ML_COMMENT"
    public final void mRULE_ML_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_ML_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:186:17: ( '/*' ( options {greedy=false; } : . )* '*/' )
            // InternalProblemLexer.g:186:19: '/*' ( options {greedy=false; } : . )* '*/'
            {
            match("/*"); 

            // InternalProblemLexer.g:186:24: ( options {greedy=false; } : . )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0=='*') ) {
                    int LA10_1 = input.LA(2);

                    if ( (LA10_1=='/') ) {
                        alt10=2;
                    }
                    else if ( ((LA10_1>='\u0000' && LA10_1<='.')||(LA10_1>='0' && LA10_1<='\uFFFF')) ) {
                        alt10=1;
                    }


                }
                else if ( ((LA10_0>='\u0000' && LA10_0<=')')||(LA10_0>='+' && LA10_0<='\uFFFF')) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // InternalProblemLexer.g:186:52: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);

            match("*/"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_ML_COMMENT"

    // $ANTLR start "RULE_WS"
    public final void mRULE_WS() throws RecognitionException {
        try {
            int _type = RULE_WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:188:9: ( ( ' ' | '\\t' | '\\r' | '\\n' )+ )
            // InternalProblemLexer.g:188:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
            {
            // InternalProblemLexer.g:188:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
            int cnt11=0;
            loop11:
            do {
                int alt11=2;
                int LA11_0 = input.LA(1);

                if ( ((LA11_0>='\t' && LA11_0<='\n')||LA11_0=='\r'||LA11_0==' ') ) {
                    alt11=1;
                }


                switch (alt11) {
            	case 1 :
            	    // InternalProblemLexer.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt11 >= 1 ) break loop11;
                        EarlyExitException eee =
                            new EarlyExitException(11, input);
                        throw eee;
                }
                cnt11++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_WS"

    // $ANTLR start "RULE_ANY_OTHER"
    public final void mRULE_ANY_OTHER() throws RecognitionException {
        try {
            int _type = RULE_ANY_OTHER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // InternalProblemLexer.g:190:16: ( . )
            // InternalProblemLexer.g:190:18: .
            {
            matchAny(); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_ANY_OTHER"

    public void mTokens() throws RecognitionException {
        // InternalProblemLexer.g:1:8: ( Concretization | Propagation | Aggregator | Candidate | Container | Primitive | Abstract | Contains | Datatype | Decision | Opposite | Declare | Default | Extends | Partial | Problem | Subsets | Unknown | Assert | Import | Module | Refers | Shadow | Class | Error | False | Multi | Scope | Atom | Enum | Must | Pred | Rule | True | ExclamationMarkEqualsSignEqualsSign | LessThanSignHyphenMinusGreaterThanSign | EqualsSignEqualsSignEqualsSign | EqualsSignEqualsSignGreaterThanSign | May | ExclamationMarkEqualsSign | AmpersandAmpersand | AsteriskAsterisk | PlusSignEqualsSign | HyphenMinusGreaterThanSign | FullStopFullStop | SolidusReverseSolidus | ColonColon | ColonGreaterThanSign | LessThanSignColon | LessThanSignEqualsSign | EqualsSignEqualsSign | GreaterThanSignEqualsSign | ReverseSolidusSolidus | CircumflexAccentCircumflexAccent | As | Is | VerticalLineVerticalLine | ExclamationMark | NumberSign | LeftParenthesis | RightParenthesis | Asterisk | PlusSign | Comma | HyphenMinus | FullStop | Solidus | Colon | Semicolon | LessThanSign | EqualsSign | GreaterThanSign | QuestionMark | CommercialAt | LeftSquareBracket | RightSquareBracket | LeftCurlyBracket | RightCurlyBracket | RULE_QUALIFIED_NAME_SEPARATOR | RULE_ID | RULE_EXPONENTIAL | RULE_SL_COMMENT | RULE_STRING | RULE_QUOTED_ID | RULE_INT | RULE_ML_COMMENT | RULE_WS | RULE_ANY_OTHER )
        int alt12=88;
        alt12 = dfa12.predict(input);
        switch (alt12) {
            case 1 :
                // InternalProblemLexer.g:1:10: Concretization
                {
                mConcretization(); 

                }
                break;
            case 2 :
                // InternalProblemLexer.g:1:25: Propagation
                {
                mPropagation(); 

                }
                break;
            case 3 :
                // InternalProblemLexer.g:1:37: Aggregator
                {
                mAggregator(); 

                }
                break;
            case 4 :
                // InternalProblemLexer.g:1:48: Candidate
                {
                mCandidate(); 

                }
                break;
            case 5 :
                // InternalProblemLexer.g:1:58: Container
                {
                mContainer(); 

                }
                break;
            case 6 :
                // InternalProblemLexer.g:1:68: Primitive
                {
                mPrimitive(); 

                }
                break;
            case 7 :
                // InternalProblemLexer.g:1:78: Abstract
                {
                mAbstract(); 

                }
                break;
            case 8 :
                // InternalProblemLexer.g:1:87: Contains
                {
                mContains(); 

                }
                break;
            case 9 :
                // InternalProblemLexer.g:1:96: Datatype
                {
                mDatatype(); 

                }
                break;
            case 10 :
                // InternalProblemLexer.g:1:105: Decision
                {
                mDecision(); 

                }
                break;
            case 11 :
                // InternalProblemLexer.g:1:114: Opposite
                {
                mOpposite(); 

                }
                break;
            case 12 :
                // InternalProblemLexer.g:1:123: Declare
                {
                mDeclare(); 

                }
                break;
            case 13 :
                // InternalProblemLexer.g:1:131: Default
                {
                mDefault(); 

                }
                break;
            case 14 :
                // InternalProblemLexer.g:1:139: Extends
                {
                mExtends(); 

                }
                break;
            case 15 :
                // InternalProblemLexer.g:1:147: Partial
                {
                mPartial(); 

                }
                break;
            case 16 :
                // InternalProblemLexer.g:1:155: Problem
                {
                mProblem(); 

                }
                break;
            case 17 :
                // InternalProblemLexer.g:1:163: Subsets
                {
                mSubsets(); 

                }
                break;
            case 18 :
                // InternalProblemLexer.g:1:171: Unknown
                {
                mUnknown(); 

                }
                break;
            case 19 :
                // InternalProblemLexer.g:1:179: Assert
                {
                mAssert(); 

                }
                break;
            case 20 :
                // InternalProblemLexer.g:1:186: Import
                {
                mImport(); 

                }
                break;
            case 21 :
                // InternalProblemLexer.g:1:193: Module
                {
                mModule(); 

                }
                break;
            case 22 :
                // InternalProblemLexer.g:1:200: Refers
                {
                mRefers(); 

                }
                break;
            case 23 :
                // InternalProblemLexer.g:1:207: Shadow
                {
                mShadow(); 

                }
                break;
            case 24 :
                // InternalProblemLexer.g:1:214: Class
                {
                mClass(); 

                }
                break;
            case 25 :
                // InternalProblemLexer.g:1:220: Error
                {
                mError(); 

                }
                break;
            case 26 :
                // InternalProblemLexer.g:1:226: False
                {
                mFalse(); 

                }
                break;
            case 27 :
                // InternalProblemLexer.g:1:232: Multi
                {
                mMulti(); 

                }
                break;
            case 28 :
                // InternalProblemLexer.g:1:238: Scope
                {
                mScope(); 

                }
                break;
            case 29 :
                // InternalProblemLexer.g:1:244: Atom
                {
                mAtom(); 

                }
                break;
            case 30 :
                // InternalProblemLexer.g:1:249: Enum
                {
                mEnum(); 

                }
                break;
            case 31 :
                // InternalProblemLexer.g:1:254: Must
                {
                mMust(); 

                }
                break;
            case 32 :
                // InternalProblemLexer.g:1:259: Pred
                {
                mPred(); 

                }
                break;
            case 33 :
                // InternalProblemLexer.g:1:264: Rule
                {
                mRule(); 

                }
                break;
            case 34 :
                // InternalProblemLexer.g:1:269: True
                {
                mTrue(); 

                }
                break;
            case 35 :
                // InternalProblemLexer.g:1:274: ExclamationMarkEqualsSignEqualsSign
                {
                mExclamationMarkEqualsSignEqualsSign(); 

                }
                break;
            case 36 :
                // InternalProblemLexer.g:1:310: LessThanSignHyphenMinusGreaterThanSign
                {
                mLessThanSignHyphenMinusGreaterThanSign(); 

                }
                break;
            case 37 :
                // InternalProblemLexer.g:1:349: EqualsSignEqualsSignEqualsSign
                {
                mEqualsSignEqualsSignEqualsSign(); 

                }
                break;
            case 38 :
                // InternalProblemLexer.g:1:380: EqualsSignEqualsSignGreaterThanSign
                {
                mEqualsSignEqualsSignGreaterThanSign(); 

                }
                break;
            case 39 :
                // InternalProblemLexer.g:1:416: May
                {
                mMay(); 

                }
                break;
            case 40 :
                // InternalProblemLexer.g:1:420: ExclamationMarkEqualsSign
                {
                mExclamationMarkEqualsSign(); 

                }
                break;
            case 41 :
                // InternalProblemLexer.g:1:446: AmpersandAmpersand
                {
                mAmpersandAmpersand(); 

                }
                break;
            case 42 :
                // InternalProblemLexer.g:1:465: AsteriskAsterisk
                {
                mAsteriskAsterisk(); 

                }
                break;
            case 43 :
                // InternalProblemLexer.g:1:482: PlusSignEqualsSign
                {
                mPlusSignEqualsSign(); 

                }
                break;
            case 44 :
                // InternalProblemLexer.g:1:501: HyphenMinusGreaterThanSign
                {
                mHyphenMinusGreaterThanSign(); 

                }
                break;
            case 45 :
                // InternalProblemLexer.g:1:528: FullStopFullStop
                {
                mFullStopFullStop(); 

                }
                break;
            case 46 :
                // InternalProblemLexer.g:1:545: SolidusReverseSolidus
                {
                mSolidusReverseSolidus(); 

                }
                break;
            case 47 :
                // InternalProblemLexer.g:1:567: ColonColon
                {
                mColonColon(); 

                }
                break;
            case 48 :
                // InternalProblemLexer.g:1:578: ColonGreaterThanSign
                {
                mColonGreaterThanSign(); 

                }
                break;
            case 49 :
                // InternalProblemLexer.g:1:599: LessThanSignColon
                {
                mLessThanSignColon(); 

                }
                break;
            case 50 :
                // InternalProblemLexer.g:1:617: LessThanSignEqualsSign
                {
                mLessThanSignEqualsSign(); 

                }
                break;
            case 51 :
                // InternalProblemLexer.g:1:640: EqualsSignEqualsSign
                {
                mEqualsSignEqualsSign(); 

                }
                break;
            case 52 :
                // InternalProblemLexer.g:1:661: GreaterThanSignEqualsSign
                {
                mGreaterThanSignEqualsSign(); 

                }
                break;
            case 53 :
                // InternalProblemLexer.g:1:687: ReverseSolidusSolidus
                {
                mReverseSolidusSolidus(); 

                }
                break;
            case 54 :
                // InternalProblemLexer.g:1:709: CircumflexAccentCircumflexAccent
                {
                mCircumflexAccentCircumflexAccent(); 

                }
                break;
            case 55 :
                // InternalProblemLexer.g:1:742: As
                {
                mAs(); 

                }
                break;
            case 56 :
                // InternalProblemLexer.g:1:745: Is
                {
                mIs(); 

                }
                break;
            case 57 :
                // InternalProblemLexer.g:1:748: VerticalLineVerticalLine
                {
                mVerticalLineVerticalLine(); 

                }
                break;
            case 58 :
                // InternalProblemLexer.g:1:773: ExclamationMark
                {
                mExclamationMark(); 

                }
                break;
            case 59 :
                // InternalProblemLexer.g:1:789: NumberSign
                {
                mNumberSign(); 

                }
                break;
            case 60 :
                // InternalProblemLexer.g:1:800: LeftParenthesis
                {
                mLeftParenthesis(); 

                }
                break;
            case 61 :
                // InternalProblemLexer.g:1:816: RightParenthesis
                {
                mRightParenthesis(); 

                }
                break;
            case 62 :
                // InternalProblemLexer.g:1:833: Asterisk
                {
                mAsterisk(); 

                }
                break;
            case 63 :
                // InternalProblemLexer.g:1:842: PlusSign
                {
                mPlusSign(); 

                }
                break;
            case 64 :
                // InternalProblemLexer.g:1:851: Comma
                {
                mComma(); 

                }
                break;
            case 65 :
                // InternalProblemLexer.g:1:857: HyphenMinus
                {
                mHyphenMinus(); 

                }
                break;
            case 66 :
                // InternalProblemLexer.g:1:869: FullStop
                {
                mFullStop(); 

                }
                break;
            case 67 :
                // InternalProblemLexer.g:1:878: Solidus
                {
                mSolidus(); 

                }
                break;
            case 68 :
                // InternalProblemLexer.g:1:886: Colon
                {
                mColon(); 

                }
                break;
            case 69 :
                // InternalProblemLexer.g:1:892: Semicolon
                {
                mSemicolon(); 

                }
                break;
            case 70 :
                // InternalProblemLexer.g:1:902: LessThanSign
                {
                mLessThanSign(); 

                }
                break;
            case 71 :
                // InternalProblemLexer.g:1:915: EqualsSign
                {
                mEqualsSign(); 

                }
                break;
            case 72 :
                // InternalProblemLexer.g:1:926: GreaterThanSign
                {
                mGreaterThanSign(); 

                }
                break;
            case 73 :
                // InternalProblemLexer.g:1:942: QuestionMark
                {
                mQuestionMark(); 

                }
                break;
            case 74 :
                // InternalProblemLexer.g:1:955: CommercialAt
                {
                mCommercialAt(); 

                }
                break;
            case 75 :
                // InternalProblemLexer.g:1:968: LeftSquareBracket
                {
                mLeftSquareBracket(); 

                }
                break;
            case 76 :
                // InternalProblemLexer.g:1:986: RightSquareBracket
                {
                mRightSquareBracket(); 

                }
                break;
            case 77 :
                // InternalProblemLexer.g:1:1005: LeftCurlyBracket
                {
                mLeftCurlyBracket(); 

                }
                break;
            case 78 :
                // InternalProblemLexer.g:1:1022: RightCurlyBracket
                {
                mRightCurlyBracket(); 

                }
                break;
            case 79 :
                // InternalProblemLexer.g:1:1040: RULE_QUALIFIED_NAME_SEPARATOR
                {
                mRULE_QUALIFIED_NAME_SEPARATOR(); 

                }
                break;
            case 80 :
                // InternalProblemLexer.g:1:1070: RULE_ID
                {
                mRULE_ID(); 

                }
                break;
            case 81 :
                // InternalProblemLexer.g:1:1078: RULE_EXPONENTIAL
                {
                mRULE_EXPONENTIAL(); 

                }
                break;
            case 82 :
                // InternalProblemLexer.g:1:1095: RULE_SL_COMMENT
                {
                mRULE_SL_COMMENT(); 

                }
                break;
            case 83 :
                // InternalProblemLexer.g:1:1111: RULE_STRING
                {
                mRULE_STRING(); 

                }
                break;
            case 84 :
                // InternalProblemLexer.g:1:1123: RULE_QUOTED_ID
                {
                mRULE_QUOTED_ID(); 

                }
                break;
            case 85 :
                // InternalProblemLexer.g:1:1138: RULE_INT
                {
                mRULE_INT(); 

                }
                break;
            case 86 :
                // InternalProblemLexer.g:1:1147: RULE_ML_COMMENT
                {
                mRULE_ML_COMMENT(); 

                }
                break;
            case 87 :
                // InternalProblemLexer.g:1:1163: RULE_WS
                {
                mRULE_WS(); 

                }
                break;
            case 88 :
                // InternalProblemLexer.g:1:1171: RULE_ANY_OTHER
                {
                mRULE_ANY_OTHER(); 

                }
                break;

        }

    }


    protected DFA12 dfa12 = new DFA12(this);
    static final String DFA12_eotS =
        "\1\uffff\15\61\1\115\1\121\1\123\1\55\1\126\1\130\1\132\1\134\1\140\1\143\1\145\3\55\14\uffff\1\164\1\uffff\2\55\2\uffff\3\61\1\uffff\4\61\1\u0084\15\61\1\u0093\7\61\1\u009d\5\uffff\1\u00a0\43\uffff\1\164\3\uffff\12\61\1\uffff\16\61\1\uffff\3\61\1\u00bf\4\61\5\uffff\7\61\1\u00cb\4\61\1\u00d0\7\61\1\u00d8\10\61\1\u00e1\1\uffff\1\61\1\u00e3\1\61\1\u00e5\3\61\1\u00e9\3\61\1\uffff\4\61\1\uffff\6\61\1\u00f7\1\uffff\2\61\1\u00fa\4\61\1\u00ff\1\uffff\1\61\1\uffff\1\u0101\1\uffff\3\61\1\uffff\6\61\1\u010b\6\61\1\uffff\1\61\1\u0113\1\uffff\2\61\1\u0116\1\u0117\1\uffff\1\u0118\1\uffff\4\61\1\u011e\1\61\1\u0120\2\61\1\uffff\2\61\1\u0125\1\u0126\1\61\1\u0128\1\u0129\1\uffff\1\61\1\u012b\3\uffff\2\61\1\u012e\2\61\1\uffff\1\61\1\uffff\1\61\1\u0133\1\u0134\1\u0135\2\uffff\1\u0136\2\uffff\1\61\1\uffff\1\61\1\u0139\1\uffff\1\u013a\1\61\1\u013c\1\61\4\uffff\2\61\2\uffff\1\61\1\uffff\1\u0141\1\uffff\1\61\1\u0143\1\uffff\1\61\1\uffff\1\61\1\u0146\1\uffff";
    static final String DFA12_eofS =
        "\u0147\uffff";
    static final String DFA12_minS =
        "\1\0\2\141\1\142\1\141\1\160\1\156\1\143\1\156\1\155\1\141\1\145\1\141\1\162\1\75\1\55\1\75\1\46\1\52\1\75\1\76\1\56\1\52\1\72\1\75\1\57\1\136\1\174\14\uffff\1\60\1\uffff\2\0\2\uffff\2\156\1\141\1\uffff\1\145\1\162\1\147\1\163\1\60\1\157\1\164\1\143\1\160\1\164\1\162\1\165\1\142\1\141\1\157\1\156\1\153\1\160\1\60\1\144\1\154\1\171\1\146\2\154\1\165\1\75\5\uffff\1\75\43\uffff\1\60\3\uffff\1\143\1\144\1\163\1\142\1\155\1\144\1\164\1\162\1\164\1\145\1\uffff\1\155\1\141\1\151\1\141\1\157\1\145\1\157\1\155\1\163\1\144\1\160\1\164\1\156\1\157\1\uffff\1\165\2\164\1\60\2\145\1\163\1\145\5\uffff\1\162\1\141\1\151\1\163\1\141\1\154\1\151\1\60\1\151\1\145\2\162\1\60\1\164\1\163\1\141\1\165\1\163\1\156\1\162\1\60\1\145\1\157\1\145\1\150\1\157\1\162\1\154\1\151\1\60\1\uffff\1\162\1\60\1\145\1\60\1\145\1\151\1\144\1\60\1\147\1\145\1\164\1\uffff\1\141\1\147\1\141\1\164\1\uffff\1\171\1\151\1\162\1\154\1\151\1\144\1\60\1\uffff\1\164\1\167\1\60\1\145\1\167\1\164\1\145\1\60\1\uffff\1\163\1\uffff\1\60\1\uffff\1\164\1\156\1\141\1\uffff\1\141\1\155\1\151\1\154\1\141\1\143\1\60\1\160\1\157\1\145\2\164\1\163\1\uffff\1\163\1\60\1\uffff\1\164\1\156\2\60\1\uffff\1\60\1\uffff\1\151\1\145\2\164\1\60\1\166\1\60\2\164\1\uffff\1\145\1\156\2\60\1\145\2\60\1\uffff\1\151\1\60\3\uffff\1\172\1\162\1\60\1\145\1\151\1\uffff\1\145\1\uffff\1\157\3\60\2\uffff\1\60\2\uffff\1\143\1\uffff\1\141\1\60\1\uffff\1\60\1\157\1\60\1\162\4\uffff\1\72\1\164\2\uffff\1\156\1\uffff\1\60\1\uffff\1\151\1\60\1\uffff\1\157\1\uffff\1\156\1\60\1\uffff";
    static final String DFA12_maxS =
        "\1\uffff\1\157\1\162\1\164\1\145\1\160\1\170\1\171\1\156\1\163\2\165\1\141\1\162\3\75\1\46\1\52\1\75\1\76\1\56\1\134\1\76\1\75\1\57\1\136\1\174\14\uffff\1\145\1\uffff\2\uffff\2\uffff\2\156\1\141\1\uffff\1\157\1\162\1\147\1\163\1\172\1\157\1\164\1\146\1\160\1\164\1\162\1\165\1\142\1\141\1\157\1\156\1\153\1\160\1\172\1\144\1\163\1\171\1\146\2\154\1\165\1\75\5\uffff\1\76\43\uffff\1\145\3\uffff\1\164\1\144\1\163\1\160\1\155\1\144\1\164\1\162\1\164\1\145\1\uffff\1\155\1\141\1\154\1\141\1\157\1\145\1\157\1\155\1\163\1\144\1\160\1\164\1\156\1\157\1\uffff\1\165\2\164\1\172\2\145\1\163\1\145\5\uffff\1\162\1\141\1\151\1\163\1\141\1\154\1\151\1\172\1\151\1\145\2\162\1\172\1\164\1\163\1\141\1\165\1\163\1\156\1\162\1\172\1\145\1\157\1\145\1\150\1\157\1\162\1\154\1\151\1\172\1\uffff\1\162\1\172\1\145\1\172\1\145\1\151\1\144\1\172\1\147\1\145\1\164\1\uffff\1\141\1\147\1\141\1\164\1\uffff\1\171\1\151\1\162\1\154\1\151\1\144\1\172\1\uffff\1\164\1\167\1\172\1\145\1\167\1\164\1\145\1\172\1\uffff\1\163\1\uffff\1\172\1\uffff\1\164\1\156\1\141\1\uffff\1\141\1\155\1\151\1\154\1\141\1\143\1\172\1\160\1\157\1\145\2\164\1\163\1\uffff\1\163\1\172\1\uffff\1\164\1\156\2\172\1\uffff\1\172\1\uffff\1\151\1\163\2\164\1\172\1\166\1\172\2\164\1\uffff\1\145\1\156\2\172\1\145\2\172\1\uffff\1\151\1\172\3\uffff\1\172\1\162\1\172\1\145\1\151\1\uffff\1\145\1\uffff\1\157\3\172\2\uffff\1\172\2\uffff\1\143\1\uffff\1\141\1\172\1\uffff\1\172\1\157\1\172\1\162\4\uffff\1\72\1\164\2\uffff\1\156\1\uffff\1\172\1\uffff\1\151\1\172\1\uffff\1\157\1\uffff\1\156\1\172\1\uffff";
    static final String DFA12_acceptS =
        "\34\uffff\1\73\1\74\1\75\1\100\1\105\1\111\1\112\1\113\1\114\1\115\1\116\1\120\1\uffff\1\122\2\uffff\1\127\1\130\3\uffff\1\120\33\uffff\1\72\1\44\1\61\1\62\1\106\1\uffff\1\107\1\51\1\52\1\76\1\53\1\77\1\54\1\101\1\55\1\102\1\56\1\122\1\126\1\103\1\57\1\60\1\104\1\64\1\110\1\65\1\66\1\71\1\73\1\74\1\75\1\100\1\105\1\111\1\112\1\113\1\114\1\115\1\116\1\125\1\121\1\uffff\1\123\1\124\1\127\12\uffff\1\67\16\uffff\1\70\10\uffff\1\43\1\50\1\45\1\46\1\63\36\uffff\1\47\13\uffff\1\40\4\uffff\1\35\7\uffff\1\36\10\uffff\1\37\1\uffff\1\41\1\uffff\1\42\3\uffff\1\30\15\uffff\1\31\2\uffff\1\34\4\uffff\1\33\1\uffff\1\32\11\uffff\1\23\7\uffff\1\27\2\uffff\1\24\1\25\1\26\5\uffff\1\20\1\uffff\1\17\4\uffff\1\14\1\15\1\uffff\1\16\1\21\1\uffff\1\22\2\uffff\1\10\4\uffff\1\7\1\11\1\12\1\13\2\uffff\1\5\1\4\1\uffff\1\6\1\uffff\1\117\2\uffff\1\3\1\uffff\1\2\2\uffff\1\1";
    static final String DFA12_specialS =
        "\1\1\51\uffff\1\2\1\0\u011b\uffff}>";
    static final String[] DFA12_transitionS = {
            "\11\55\2\54\2\55\1\54\22\55\1\54\1\16\1\52\1\34\1\55\1\51\1\21\1\53\1\35\1\36\1\22\1\23\1\37\1\24\1\25\1\26\12\50\1\27\1\40\1\17\1\20\1\30\1\41\1\42\32\47\1\43\1\31\1\44\1\32\1\47\1\55\1\3\1\47\1\1\1\4\1\6\1\14\2\47\1\11\3\47\1\12\1\47\1\5\1\2\1\47\1\13\1\7\1\15\1\10\5\47\1\45\1\33\1\46\uff82\55",
            "\1\57\12\uffff\1\60\2\uffff\1\56",
            "\1\63\20\uffff\1\62",
            "\1\65\4\uffff\1\64\13\uffff\1\66\1\67",
            "\1\70\3\uffff\1\71",
            "\1\72",
            "\1\75\3\uffff\1\74\5\uffff\1\73",
            "\1\100\4\uffff\1\77\14\uffff\1\76\3\uffff\1\101",
            "\1\102",
            "\1\103\5\uffff\1\104",
            "\1\107\15\uffff\1\105\5\uffff\1\106",
            "\1\110\17\uffff\1\111",
            "\1\112",
            "\1\113",
            "\1\114",
            "\1\116\14\uffff\1\117\2\uffff\1\120",
            "\1\122",
            "\1\124",
            "\1\125",
            "\1\127",
            "\1\131",
            "\1\133",
            "\1\137\4\uffff\1\136\54\uffff\1\135",
            "\1\141\3\uffff\1\142",
            "\1\144",
            "\1\146",
            "\1\147",
            "\1\150",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\12\166\13\uffff\1\165\37\uffff\1\165",
            "",
            "\0\167",
            "\0\170",
            "",
            "",
            "\1\172",
            "\1\173",
            "\1\174",
            "",
            "\1\177\3\uffff\1\176\5\uffff\1\175",
            "\1\u0080",
            "\1\u0081",
            "\1\u0082",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\22\61\1\u0083\7\61",
            "\1\u0085",
            "\1\u0086",
            "\1\u0087\2\uffff\1\u0088",
            "\1\u0089",
            "\1\u008a",
            "\1\u008b",
            "\1\u008c",
            "\1\u008d",
            "\1\u008e",
            "\1\u008f",
            "\1\u0090",
            "\1\u0091",
            "\1\u0092",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u0094",
            "\1\u0095\6\uffff\1\u0096",
            "\1\u0097",
            "\1\u0098",
            "\1\u0099",
            "\1\u009a",
            "\1\u009b",
            "\1\u009c",
            "",
            "",
            "",
            "",
            "",
            "\1\u009e\1\u009f",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\12\166\13\uffff\1\165\37\uffff\1\165",
            "",
            "",
            "",
            "\1\u00a1\20\uffff\1\u00a2",
            "\1\u00a3",
            "\1\u00a4",
            "\1\u00a6\15\uffff\1\u00a5",
            "\1\u00a7",
            "\1\u00a8",
            "\1\u00a9",
            "\1\u00aa",
            "\1\u00ab",
            "\1\u00ac",
            "",
            "\1\u00ad",
            "\1\u00ae",
            "\1\u00af\2\uffff\1\u00b0",
            "\1\u00b1",
            "\1\u00b2",
            "\1\u00b3",
            "\1\u00b4",
            "\1\u00b5",
            "\1\u00b6",
            "\1\u00b7",
            "\1\u00b8",
            "\1\u00b9",
            "\1\u00ba",
            "\1\u00bb",
            "",
            "\1\u00bc",
            "\1\u00bd",
            "\1\u00be",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00c0",
            "\1\u00c1",
            "\1\u00c2",
            "\1\u00c3",
            "",
            "",
            "",
            "",
            "",
            "\1\u00c4",
            "\1\u00c5",
            "\1\u00c6",
            "\1\u00c7",
            "\1\u00c8",
            "\1\u00c9",
            "\1\u00ca",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00cc",
            "\1\u00cd",
            "\1\u00ce",
            "\1\u00cf",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00d1",
            "\1\u00d2",
            "\1\u00d3",
            "\1\u00d4",
            "\1\u00d5",
            "\1\u00d6",
            "\1\u00d7",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00d9",
            "\1\u00da",
            "\1\u00db",
            "\1\u00dc",
            "\1\u00dd",
            "\1\u00de",
            "\1\u00df",
            "\1\u00e0",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u00e2",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00e4",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00e6",
            "\1\u00e7",
            "\1\u00e8",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00ea",
            "\1\u00eb",
            "\1\u00ec",
            "",
            "\1\u00ed",
            "\1\u00ee",
            "\1\u00ef",
            "\1\u00f0",
            "",
            "\1\u00f1",
            "\1\u00f2",
            "\1\u00f3",
            "\1\u00f4",
            "\1\u00f5",
            "\1\u00f6",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u00f8",
            "\1\u00f9",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u00fb",
            "\1\u00fc",
            "\1\u00fd",
            "\1\u00fe",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0100",
            "",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0102",
            "\1\u0103",
            "\1\u0104",
            "",
            "\1\u0105",
            "\1\u0106",
            "\1\u0107",
            "\1\u0108",
            "\1\u0109",
            "\1\u010a",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u010c",
            "\1\u010d",
            "\1\u010e",
            "\1\u010f",
            "\1\u0110",
            "\1\u0111",
            "",
            "\1\u0112",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0114",
            "\1\u0115",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0119",
            "\1\u011a\15\uffff\1\u011b",
            "\1\u011c",
            "\1\u011d",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u011f",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u0121",
            "\1\u0122",
            "",
            "\1\u0123",
            "\1\u0124",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u0127",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u012a",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "",
            "",
            "\1\u012c",
            "\1\u012d",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u012f",
            "\1\u0130",
            "",
            "\1\u0131",
            "",
            "\1\u0132",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "",
            "\1\u0137",
            "",
            "\1\u0138",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u013b",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "\1\u013d",
            "",
            "",
            "",
            "",
            "\1\u013e",
            "\1\u013f",
            "",
            "",
            "\1\u0140",
            "",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0142",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            "",
            "\1\u0144",
            "",
            "\1\u0145",
            "\12\61\7\uffff\32\61\4\uffff\1\61\1\uffff\32\61",
            ""
    };

    static final short[] DFA12_eot = DFA.unpackEncodedString(DFA12_eotS);
    static final short[] DFA12_eof = DFA.unpackEncodedString(DFA12_eofS);
    static final char[] DFA12_min = DFA.unpackEncodedStringToUnsignedChars(DFA12_minS);
    static final char[] DFA12_max = DFA.unpackEncodedStringToUnsignedChars(DFA12_maxS);
    static final short[] DFA12_accept = DFA.unpackEncodedString(DFA12_acceptS);
    static final short[] DFA12_special = DFA.unpackEncodedString(DFA12_specialS);
    static final short[][] DFA12_transition;

    static {
        int numStates = DFA12_transitionS.length;
        DFA12_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA12_transition[i] = DFA.unpackEncodedString(DFA12_transitionS[i]);
        }
    }

    class DFA12 extends DFA {

        public DFA12(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 12;
            this.eot = DFA12_eot;
            this.eof = DFA12_eof;
            this.min = DFA12_min;
            this.max = DFA12_max;
            this.accept = DFA12_accept;
            this.special = DFA12_special;
            this.transition = DFA12_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( Concretization | Propagation | Aggregator | Candidate | Container | Primitive | Abstract | Contains | Datatype | Decision | Opposite | Declare | Default | Extends | Partial | Problem | Subsets | Unknown | Assert | Import | Module | Refers | Shadow | Class | Error | False | Multi | Scope | Atom | Enum | Must | Pred | Rule | True | ExclamationMarkEqualsSignEqualsSign | LessThanSignHyphenMinusGreaterThanSign | EqualsSignEqualsSignEqualsSign | EqualsSignEqualsSignGreaterThanSign | May | ExclamationMarkEqualsSign | AmpersandAmpersand | AsteriskAsterisk | PlusSignEqualsSign | HyphenMinusGreaterThanSign | FullStopFullStop | SolidusReverseSolidus | ColonColon | ColonGreaterThanSign | LessThanSignColon | LessThanSignEqualsSign | EqualsSignEqualsSign | GreaterThanSignEqualsSign | ReverseSolidusSolidus | CircumflexAccentCircumflexAccent | As | Is | VerticalLineVerticalLine | ExclamationMark | NumberSign | LeftParenthesis | RightParenthesis | Asterisk | PlusSign | Comma | HyphenMinus | FullStop | Solidus | Colon | Semicolon | LessThanSign | EqualsSign | GreaterThanSign | QuestionMark | CommercialAt | LeftSquareBracket | RightSquareBracket | LeftCurlyBracket | RightCurlyBracket | RULE_QUALIFIED_NAME_SEPARATOR | RULE_ID | RULE_EXPONENTIAL | RULE_SL_COMMENT | RULE_STRING | RULE_QUOTED_ID | RULE_INT | RULE_ML_COMMENT | RULE_WS | RULE_ANY_OTHER );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA12_43 = input.LA(1);

                        s = -1;
                        if ( ((LA12_43>='\u0000' && LA12_43<='\uFFFF')) ) {s = 120;}

                        else s = 45;

                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA12_0 = input.LA(1);

                        s = -1;
                        if ( (LA12_0=='c') ) {s = 1;}

                        else if ( (LA12_0=='p') ) {s = 2;}

                        else if ( (LA12_0=='a') ) {s = 3;}

                        else if ( (LA12_0=='d') ) {s = 4;}

                        else if ( (LA12_0=='o') ) {s = 5;}

                        else if ( (LA12_0=='e') ) {s = 6;}

                        else if ( (LA12_0=='s') ) {s = 7;}

                        else if ( (LA12_0=='u') ) {s = 8;}

                        else if ( (LA12_0=='i') ) {s = 9;}

                        else if ( (LA12_0=='m') ) {s = 10;}

                        else if ( (LA12_0=='r') ) {s = 11;}

                        else if ( (LA12_0=='f') ) {s = 12;}

                        else if ( (LA12_0=='t') ) {s = 13;}

                        else if ( (LA12_0=='!') ) {s = 14;}

                        else if ( (LA12_0=='<') ) {s = 15;}

                        else if ( (LA12_0=='=') ) {s = 16;}

                        else if ( (LA12_0=='&') ) {s = 17;}

                        else if ( (LA12_0=='*') ) {s = 18;}

                        else if ( (LA12_0=='+') ) {s = 19;}

                        else if ( (LA12_0=='-') ) {s = 20;}

                        else if ( (LA12_0=='.') ) {s = 21;}

                        else if ( (LA12_0=='/') ) {s = 22;}

                        else if ( (LA12_0==':') ) {s = 23;}

                        else if ( (LA12_0=='>') ) {s = 24;}

                        else if ( (LA12_0=='\\') ) {s = 25;}

                        else if ( (LA12_0=='^') ) {s = 26;}

                        else if ( (LA12_0=='|') ) {s = 27;}

                        else if ( (LA12_0=='#') ) {s = 28;}

                        else if ( (LA12_0=='(') ) {s = 29;}

                        else if ( (LA12_0==')') ) {s = 30;}

                        else if ( (LA12_0==',') ) {s = 31;}

                        else if ( (LA12_0==';') ) {s = 32;}

                        else if ( (LA12_0=='?') ) {s = 33;}

                        else if ( (LA12_0=='@') ) {s = 34;}

                        else if ( (LA12_0=='[') ) {s = 35;}

                        else if ( (LA12_0==']') ) {s = 36;}

                        else if ( (LA12_0=='{') ) {s = 37;}

                        else if ( (LA12_0=='}') ) {s = 38;}

                        else if ( ((LA12_0>='A' && LA12_0<='Z')||LA12_0=='_'||LA12_0=='b'||(LA12_0>='g' && LA12_0<='h')||(LA12_0>='j' && LA12_0<='l')||LA12_0=='n'||LA12_0=='q'||(LA12_0>='v' && LA12_0<='z')) ) {s = 39;}

                        else if ( ((LA12_0>='0' && LA12_0<='9')) ) {s = 40;}

                        else if ( (LA12_0=='%') ) {s = 41;}

                        else if ( (LA12_0=='\"') ) {s = 42;}

                        else if ( (LA12_0=='\'') ) {s = 43;}

                        else if ( ((LA12_0>='\t' && LA12_0<='\n')||LA12_0=='\r'||LA12_0==' ') ) {s = 44;}

                        else if ( ((LA12_0>='\u0000' && LA12_0<='\b')||(LA12_0>='\u000B' && LA12_0<='\f')||(LA12_0>='\u000E' && LA12_0<='\u001F')||LA12_0=='$'||LA12_0=='`'||(LA12_0>='~' && LA12_0<='\uFFFF')) ) {s = 45;}

                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA12_42 = input.LA(1);

                        s = -1;
                        if ( ((LA12_42>='\u0000' && LA12_42<='\uFFFF')) ) {s = 119;}

                        else s = 45;

                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 12, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

}