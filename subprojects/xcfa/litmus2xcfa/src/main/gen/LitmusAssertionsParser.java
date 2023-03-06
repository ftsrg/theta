// Generated from /home/solarowl/Repositories/theta/subprojects/xcfa/litmus2xcfa/src/main/antlr/LitmusAssertions.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class LitmusAssertionsParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.10.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		AssertionListExpectationTest=1, AssertionAnd=2, AssertionOr=3, AssertionExists=4, 
		AssertionFinal=5, AssertionForall=6, AssertionFilter=7, AssertionNot=8, 
		AssertionWith=9, ThreadIdentifier=10, EqualsEquals=11, NotEquals=12, LessEquals=13, 
		GreaterEquals=14, Identifier=15, DigitSequence=16, Whitespace=17, Newline=18, 
		BlockComment=19, ExecConfig=20, Excl=21, Quot=22, Num=23, Dollar=24, Percent=25, 
		Amp=26, Apos=27, LPar=28, RPar=29, Ast=30, Plus=31, Comma=32, Minus=33, 
		Period=34, Slash=35, Colon=36, Semi=37, Less=38, Equals=39, Greater=40, 
		Question=41, At=42, LBracket=43, RBracket=44, BSlash=45, LBrace=46, RBrace=47, 
		Circ=48, Tilde=49, Bar=50, Underscore=51;
	public static final int
		RULE_assertionFilter = 0, RULE_assertionList = 1, RULE_assertion = 2, 
		RULE_assertionValue = 3, RULE_varName = 4, RULE_constant = 5, RULE_assertionListExpectationList = 6, 
		RULE_assertionListExpectation = 7, RULE_assertionCompare = 8, RULE_threadId = 9;
	private static String[] makeRuleNames() {
		return new String[] {
			"assertionFilter", "assertionList", "assertion", "assertionValue", "varName", 
			"constant", "assertionListExpectationList", "assertionListExpectation", 
			"assertionCompare", "threadId"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, "'/\\'", "'\\/'", "'exists'", "'final'", "'forall'", "'filter'", 
			null, "'with'", null, "'=='", "'!='", "'<='", "'>='", null, null, null, 
			null, null, null, "'!'", "'\"'", "'#'", "'$'", "'%'", "'&'", "'''", "'('", 
			"')'", "'*'", "'+'", "','", "'-'", "'.'", "'/'", "':'", "';'", "'<'", 
			"'='", "'>'", "'?'", "'@'", "'['", "']'", "'\\'", "'{'", "'}'", "'^'", 
			"'~'", "'|'", "'_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "AssertionListExpectationTest", "AssertionAnd", "AssertionOr", 
			"AssertionExists", "AssertionFinal", "AssertionForall", "AssertionFilter", 
			"AssertionNot", "AssertionWith", "ThreadIdentifier", "EqualsEquals", 
			"NotEquals", "LessEquals", "GreaterEquals", "Identifier", "DigitSequence", 
			"Whitespace", "Newline", "BlockComment", "ExecConfig", "Excl", "Quot", 
			"Num", "Dollar", "Percent", "Amp", "Apos", "LPar", "RPar", "Ast", "Plus", 
			"Comma", "Minus", "Period", "Slash", "Colon", "Semi", "Less", "Equals", 
			"Greater", "Question", "At", "LBracket", "RBracket", "BSlash", "LBrace", 
			"RBrace", "Circ", "Tilde", "Bar", "Underscore"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "LitmusAssertions.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public LitmusAssertionsParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class AssertionFilterContext extends ParserRuleContext {
		public AssertionContext a;
		public TerminalNode AssertionFilter() { return getToken(LitmusAssertionsParser.AssertionFilter, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public AssertionFilterContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionFilter; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionFilter(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionFilter(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionFilter(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionFilterContext assertionFilter() throws RecognitionException {
		AssertionFilterContext _localctx = new AssertionFilterContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_assertionFilter);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(20);
			match(AssertionFilter);
			setState(21);
			((AssertionFilterContext)_localctx).a = assertion(0);
			setState(23);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==Semi) {
				{
				setState(22);
				match(Semi);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListContext extends ParserRuleContext {
		public AssertionContext a;
		public TerminalNode AssertionExists() { return getToken(LitmusAssertionsParser.AssertionExists, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public TerminalNode AssertionForall() { return getToken(LitmusAssertionsParser.AssertionForall, 0); }
		public TerminalNode AssertionFinal() { return getToken(LitmusAssertionsParser.AssertionFinal, 0); }
		public AssertionListExpectationListContext assertionListExpectationList() {
			return getRuleContext(AssertionListExpectationListContext.class,0);
		}
		public AssertionListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListContext assertionList() throws RecognitionException {
		AssertionListContext _localctx = new AssertionListContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_assertionList);
		int _la;
		try {
			setState(48);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case AssertionExists:
				enterOuterAlt(_localctx, 1);
				{
				setState(25);
				match(AssertionExists);
				setState(26);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(28);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(27);
					match(Semi);
					}
				}

				}
				break;
			case AssertionNot:
				enterOuterAlt(_localctx, 2);
				{
				setState(30);
				match(AssertionNot);
				setState(31);
				match(AssertionExists);
				setState(32);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(34);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(33);
					match(Semi);
					}
				}

				}
				break;
			case AssertionForall:
				enterOuterAlt(_localctx, 3);
				{
				setState(36);
				match(AssertionForall);
				setState(37);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(39);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(38);
					match(Semi);
					}
				}

				}
				break;
			case AssertionFinal:
				enterOuterAlt(_localctx, 4);
				{
				setState(41);
				match(AssertionFinal);
				setState(42);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(44);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(43);
					match(Semi);
					}
				}

				setState(46);
				assertionListExpectationList();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionContext extends ParserRuleContext {
		public AssertionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertion; }
	 
		public AssertionContext() { }
		public void copyFrom(AssertionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class AssertionBasicContext extends AssertionContext {
		public List<AssertionValueContext> assertionValue() {
			return getRuleContexts(AssertionValueContext.class);
		}
		public AssertionValueContext assertionValue(int i) {
			return getRuleContext(AssertionValueContext.class,i);
		}
		public AssertionCompareContext assertionCompare() {
			return getRuleContext(AssertionCompareContext.class,0);
		}
		public AssertionBasicContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionBasic(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionBasic(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionBasic(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionAndContext extends AssertionContext {
		public List<AssertionContext> assertion() {
			return getRuleContexts(AssertionContext.class);
		}
		public AssertionContext assertion(int i) {
			return getRuleContext(AssertionContext.class,i);
		}
		public TerminalNode AssertionAnd() { return getToken(LitmusAssertionsParser.AssertionAnd, 0); }
		public AssertionAndContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionAnd(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionAnd(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionAnd(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionOrContext extends AssertionContext {
		public List<AssertionContext> assertion() {
			return getRuleContexts(AssertionContext.class);
		}
		public AssertionContext assertion(int i) {
			return getRuleContext(AssertionContext.class,i);
		}
		public TerminalNode AssertionOr() { return getToken(LitmusAssertionsParser.AssertionOr, 0); }
		public AssertionOrContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionOr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionOr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionOr(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionParenthesisContext extends AssertionContext {
		public TerminalNode LPar() { return getToken(LitmusAssertionsParser.LPar, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode RPar() { return getToken(LitmusAssertionsParser.RPar, 0); }
		public AssertionParenthesisContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionParenthesis(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionParenthesis(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionParenthesis(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionNotContext extends AssertionContext {
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public AssertionNotContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionNot(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionNot(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionNot(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionContext assertion() throws RecognitionException {
		return assertion(0);
	}

	private AssertionContext assertion(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		AssertionContext _localctx = new AssertionContext(_ctx, _parentState);
		AssertionContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_assertion, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(61);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case LPar:
				{
				_localctx = new AssertionParenthesisContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(51);
				match(LPar);
				setState(52);
				assertion(0);
				setState(53);
				match(RPar);
				}
				break;
			case AssertionNot:
				{
				_localctx = new AssertionNotContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(55);
				match(AssertionNot);
				setState(56);
				assertion(4);
				}
				break;
			case ThreadIdentifier:
			case Identifier:
			case DigitSequence:
			case Minus:
			case Underscore:
				{
				_localctx = new AssertionBasicContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(57);
				assertionValue();
				setState(58);
				assertionCompare();
				setState(59);
				assertionValue();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(71);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(69);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
					case 1:
						{
						_localctx = new AssertionAndContext(new AssertionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_assertion);
						setState(63);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(64);
						match(AssertionAnd);
						setState(65);
						assertion(4);
						}
						break;
					case 2:
						{
						_localctx = new AssertionOrContext(new AssertionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_assertion);
						setState(66);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(67);
						match(AssertionOr);
						setState(68);
						assertion(3);
						}
						break;
					}
					} 
				}
				setState(73);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class AssertionValueContext extends ParserRuleContext {
		public VarNameContext varName() {
			return getRuleContext(VarNameContext.class,0);
		}
		public TerminalNode LBracket() { return getToken(LitmusAssertionsParser.LBracket, 0); }
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public TerminalNode RBracket() { return getToken(LitmusAssertionsParser.RBracket, 0); }
		public ThreadIdContext threadId() {
			return getRuleContext(ThreadIdContext.class,0);
		}
		public TerminalNode Colon() { return getToken(LitmusAssertionsParser.Colon, 0); }
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public AssertionValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionValueContext assertionValue() throws RecognitionException {
		AssertionValueContext _localctx = new AssertionValueContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_assertionValue);
		try {
			setState(85);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(74);
				varName();
				setState(75);
				match(LBracket);
				setState(76);
				match(DigitSequence);
				setState(77);
				match(RBracket);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(79);
				varName();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(80);
				threadId();
				setState(81);
				match(Colon);
				setState(82);
				varName();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(84);
				constant();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarNameContext extends ParserRuleContext {
		public List<TerminalNode> Identifier() { return getTokens(LitmusAssertionsParser.Identifier); }
		public TerminalNode Identifier(int i) {
			return getToken(LitmusAssertionsParser.Identifier, i);
		}
		public List<TerminalNode> Underscore() { return getTokens(LitmusAssertionsParser.Underscore); }
		public TerminalNode Underscore(int i) {
			return getToken(LitmusAssertionsParser.Underscore, i);
		}
		public List<TerminalNode> DigitSequence() { return getTokens(LitmusAssertionsParser.DigitSequence); }
		public TerminalNode DigitSequence(int i) {
			return getToken(LitmusAssertionsParser.DigitSequence, i);
		}
		public VarNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterVarName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitVarName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitVarName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarNameContext varName() throws RecognitionException {
		VarNameContext _localctx = new VarNameContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_varName);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(90);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==Underscore) {
				{
				{
				setState(87);
				match(Underscore);
				}
				}
				setState(92);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(93);
			match(Identifier);
			setState(97);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,11,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(94);
					_la = _input.LA(1);
					if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << Identifier) | (1L << DigitSequence) | (1L << Underscore))) != 0)) ) {
					_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					}
					} 
				}
				setState(99);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,11,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstantContext extends ParserRuleContext {
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public TerminalNode Minus() { return getToken(LitmusAssertionsParser.Minus, 0); }
		public ConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstantContext constant() throws RecognitionException {
		ConstantContext _localctx = new ConstantContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_constant);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(101);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==Minus) {
				{
				setState(100);
				match(Minus);
				}
			}

			setState(103);
			match(DigitSequence);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListExpectationListContext extends ParserRuleContext {
		public TerminalNode AssertionWith() { return getToken(LitmusAssertionsParser.AssertionWith, 0); }
		public List<AssertionListExpectationContext> assertionListExpectation() {
			return getRuleContexts(AssertionListExpectationContext.class);
		}
		public AssertionListExpectationContext assertionListExpectation(int i) {
			return getRuleContext(AssertionListExpectationContext.class,i);
		}
		public AssertionListExpectationListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionListExpectationList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionListExpectationList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionListExpectationList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionListExpectationList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListExpectationListContext assertionListExpectationList() throws RecognitionException {
		AssertionListExpectationListContext _localctx = new AssertionListExpectationListContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_assertionListExpectationList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(105);
			match(AssertionWith);
			setState(107); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(106);
				assertionListExpectation();
				}
				}
				setState(109); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==AssertionListExpectationTest );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListExpectationContext extends ParserRuleContext {
		public TerminalNode AssertionListExpectationTest() { return getToken(LitmusAssertionsParser.AssertionListExpectationTest, 0); }
		public TerminalNode Colon() { return getToken(LitmusAssertionsParser.Colon, 0); }
		public TerminalNode AssertionExists() { return getToken(LitmusAssertionsParser.AssertionExists, 0); }
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public AssertionListExpectationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionListExpectation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionListExpectation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionListExpectation(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionListExpectation(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListExpectationContext assertionListExpectation() throws RecognitionException {
		AssertionListExpectationContext _localctx = new AssertionListExpectationContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_assertionListExpectation);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111);
			match(AssertionListExpectationTest);
			setState(112);
			match(Colon);
			setState(114);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==AssertionNot) {
				{
				setState(113);
				match(AssertionNot);
				}
			}

			setState(116);
			match(AssertionExists);
			setState(117);
			match(Semi);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionCompareContext extends ParserRuleContext {
		public AssertionCompareContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionCompare; }
	 
		public AssertionCompareContext() { }
		public void copyFrom(AssertionCompareContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class GeqCompareContext extends AssertionCompareContext {
		public TerminalNode GreaterEquals() { return getToken(LitmusAssertionsParser.GreaterEquals, 0); }
		public GeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterGeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitGeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitGeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NeqCompareContext extends AssertionCompareContext {
		public TerminalNode NotEquals() { return getToken(LitmusAssertionsParser.NotEquals, 0); }
		public NeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterNeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitNeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitNeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class GtCompareContext extends AssertionCompareContext {
		public TerminalNode Greater() { return getToken(LitmusAssertionsParser.Greater, 0); }
		public GtCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterGtCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitGtCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitGtCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class LtCompareContext extends AssertionCompareContext {
		public TerminalNode Less() { return getToken(LitmusAssertionsParser.Less, 0); }
		public LtCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterLtCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitLtCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitLtCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class EqCompareContext extends AssertionCompareContext {
		public TerminalNode Equals() { return getToken(LitmusAssertionsParser.Equals, 0); }
		public TerminalNode EqualsEquals() { return getToken(LitmusAssertionsParser.EqualsEquals, 0); }
		public EqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterEqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitEqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitEqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class LeqCompareContext extends AssertionCompareContext {
		public TerminalNode LessEquals() { return getToken(LitmusAssertionsParser.LessEquals, 0); }
		public LeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterLeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitLeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitLeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionCompareContext assertionCompare() throws RecognitionException {
		AssertionCompareContext _localctx = new AssertionCompareContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_assertionCompare);
		int _la;
		try {
			setState(125);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EqualsEquals:
			case Equals:
				_localctx = new EqCompareContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(119);
				_la = _input.LA(1);
				if ( !(_la==EqualsEquals || _la==Equals) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			case NotEquals:
				_localctx = new NeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(120);
				match(NotEquals);
				}
				break;
			case GreaterEquals:
				_localctx = new GeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(121);
				match(GreaterEquals);
				}
				break;
			case LessEquals:
				_localctx = new LeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(122);
				match(LessEquals);
				}
				break;
			case Less:
				_localctx = new LtCompareContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(123);
				match(Less);
				}
				break;
			case Greater:
				_localctx = new GtCompareContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(124);
				match(Greater);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ThreadIdContext extends ParserRuleContext {
		public int id;
		public Token t;
		public TerminalNode ThreadIdentifier() { return getToken(LitmusAssertionsParser.ThreadIdentifier, 0); }
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public ThreadIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_threadId; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterThreadId(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitThreadId(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitThreadId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ThreadIdContext threadId() throws RecognitionException {
		ThreadIdContext _localctx = new ThreadIdContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_threadId);
		try {
			setState(131);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ThreadIdentifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(127);
				((ThreadIdContext)_localctx).t = match(ThreadIdentifier);
				((ThreadIdContext)_localctx).id =  Integer.parseInt((((ThreadIdContext)_localctx).t!=null?((ThreadIdContext)_localctx).t.getText():null).replace("P", ""));
				}
				break;
			case DigitSequence:
				enterOuterAlt(_localctx, 2);
				{
				setState(129);
				((ThreadIdContext)_localctx).t = match(DigitSequence);
				((ThreadIdContext)_localctx).id =  Integer.parseInt((((ThreadIdContext)_localctx).t!=null?((ThreadIdContext)_localctx).t.getText():null));
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 2:
			return assertion_sempred((AssertionContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean assertion_sempred(AssertionContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 3);
		case 1:
			return precpred(_ctx, 2);
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u00013\u0086\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0002\t\u0007\t\u0001\u0000\u0001\u0000\u0001\u0000\u0003\u0000"+
		"\u0018\b\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001\u001d\b"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001#\b"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001(\b\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0003\u0001-\b\u0001\u0001\u0001\u0001"+
		"\u0001\u0003\u00011\b\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0003\u0002>\b\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002F\b\u0002\n\u0002"+
		"\f\u0002I\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0003\u0003V\b\u0003\u0001\u0004\u0005\u0004Y\b\u0004\n\u0004\f"+
		"\u0004\\\t\u0004\u0001\u0004\u0001\u0004\u0005\u0004`\b\u0004\n\u0004"+
		"\f\u0004c\t\u0004\u0001\u0005\u0003\u0005f\b\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0006\u0001\u0006\u0004\u0006l\b\u0006\u000b\u0006\f\u0006m\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0003\u0007s\b\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003"+
		"\b~\b\b\u0001\t\u0001\t\u0001\t\u0001\t\u0003\t\u0084\b\t\u0001\t\u0000"+
		"\u0001\u0004\n\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0000\u0002"+
		"\u0002\u0000\u000f\u001033\u0002\u0000\u000b\u000b\'\'\u0095\u0000\u0014"+
		"\u0001\u0000\u0000\u0000\u00020\u0001\u0000\u0000\u0000\u0004=\u0001\u0000"+
		"\u0000\u0000\u0006U\u0001\u0000\u0000\u0000\bZ\u0001\u0000\u0000\u0000"+
		"\ne\u0001\u0000\u0000\u0000\fi\u0001\u0000\u0000\u0000\u000eo\u0001\u0000"+
		"\u0000\u0000\u0010}\u0001\u0000\u0000\u0000\u0012\u0083\u0001\u0000\u0000"+
		"\u0000\u0014\u0015\u0005\u0007\u0000\u0000\u0015\u0017\u0003\u0004\u0002"+
		"\u0000\u0016\u0018\u0005%\u0000\u0000\u0017\u0016\u0001\u0000\u0000\u0000"+
		"\u0017\u0018\u0001\u0000\u0000\u0000\u0018\u0001\u0001\u0000\u0000\u0000"+
		"\u0019\u001a\u0005\u0004\u0000\u0000\u001a\u001c\u0003\u0004\u0002\u0000"+
		"\u001b\u001d\u0005%\u0000\u0000\u001c\u001b\u0001\u0000\u0000\u0000\u001c"+
		"\u001d\u0001\u0000\u0000\u0000\u001d1\u0001\u0000\u0000\u0000\u001e\u001f"+
		"\u0005\b\u0000\u0000\u001f \u0005\u0004\u0000\u0000 \"\u0003\u0004\u0002"+
		"\u0000!#\u0005%\u0000\u0000\"!\u0001\u0000\u0000\u0000\"#\u0001\u0000"+
		"\u0000\u0000#1\u0001\u0000\u0000\u0000$%\u0005\u0006\u0000\u0000%\'\u0003"+
		"\u0004\u0002\u0000&(\u0005%\u0000\u0000\'&\u0001\u0000\u0000\u0000\'("+
		"\u0001\u0000\u0000\u0000(1\u0001\u0000\u0000\u0000)*\u0005\u0005\u0000"+
		"\u0000*,\u0003\u0004\u0002\u0000+-\u0005%\u0000\u0000,+\u0001\u0000\u0000"+
		"\u0000,-\u0001\u0000\u0000\u0000-.\u0001\u0000\u0000\u0000./\u0003\f\u0006"+
		"\u0000/1\u0001\u0000\u0000\u00000\u0019\u0001\u0000\u0000\u00000\u001e"+
		"\u0001\u0000\u0000\u00000$\u0001\u0000\u0000\u00000)\u0001\u0000\u0000"+
		"\u00001\u0003\u0001\u0000\u0000\u000023\u0006\u0002\uffff\uffff\u0000"+
		"34\u0005\u001c\u0000\u000045\u0003\u0004\u0002\u000056\u0005\u001d\u0000"+
		"\u00006>\u0001\u0000\u0000\u000078\u0005\b\u0000\u00008>\u0003\u0004\u0002"+
		"\u00049:\u0003\u0006\u0003\u0000:;\u0003\u0010\b\u0000;<\u0003\u0006\u0003"+
		"\u0000<>\u0001\u0000\u0000\u0000=2\u0001\u0000\u0000\u0000=7\u0001\u0000"+
		"\u0000\u0000=9\u0001\u0000\u0000\u0000>G\u0001\u0000\u0000\u0000?@\n\u0003"+
		"\u0000\u0000@A\u0005\u0002\u0000\u0000AF\u0003\u0004\u0002\u0004BC\n\u0002"+
		"\u0000\u0000CD\u0005\u0003\u0000\u0000DF\u0003\u0004\u0002\u0003E?\u0001"+
		"\u0000\u0000\u0000EB\u0001\u0000\u0000\u0000FI\u0001\u0000\u0000\u0000"+
		"GE\u0001\u0000\u0000\u0000GH\u0001\u0000\u0000\u0000H\u0005\u0001\u0000"+
		"\u0000\u0000IG\u0001\u0000\u0000\u0000JK\u0003\b\u0004\u0000KL\u0005+"+
		"\u0000\u0000LM\u0005\u0010\u0000\u0000MN\u0005,\u0000\u0000NV\u0001\u0000"+
		"\u0000\u0000OV\u0003\b\u0004\u0000PQ\u0003\u0012\t\u0000QR\u0005$\u0000"+
		"\u0000RS\u0003\b\u0004\u0000SV\u0001\u0000\u0000\u0000TV\u0003\n\u0005"+
		"\u0000UJ\u0001\u0000\u0000\u0000UO\u0001\u0000\u0000\u0000UP\u0001\u0000"+
		"\u0000\u0000UT\u0001\u0000\u0000\u0000V\u0007\u0001\u0000\u0000\u0000"+
		"WY\u00053\u0000\u0000XW\u0001\u0000\u0000\u0000Y\\\u0001\u0000\u0000\u0000"+
		"ZX\u0001\u0000\u0000\u0000Z[\u0001\u0000\u0000\u0000[]\u0001\u0000\u0000"+
		"\u0000\\Z\u0001\u0000\u0000\u0000]a\u0005\u000f\u0000\u0000^`\u0007\u0000"+
		"\u0000\u0000_^\u0001\u0000\u0000\u0000`c\u0001\u0000\u0000\u0000a_\u0001"+
		"\u0000\u0000\u0000ab\u0001\u0000\u0000\u0000b\t\u0001\u0000\u0000\u0000"+
		"ca\u0001\u0000\u0000\u0000df\u0005!\u0000\u0000ed\u0001\u0000\u0000\u0000"+
		"ef\u0001\u0000\u0000\u0000fg\u0001\u0000\u0000\u0000gh\u0005\u0010\u0000"+
		"\u0000h\u000b\u0001\u0000\u0000\u0000ik\u0005\t\u0000\u0000jl\u0003\u000e"+
		"\u0007\u0000kj\u0001\u0000\u0000\u0000lm\u0001\u0000\u0000\u0000mk\u0001"+
		"\u0000\u0000\u0000mn\u0001\u0000\u0000\u0000n\r\u0001\u0000\u0000\u0000"+
		"op\u0005\u0001\u0000\u0000pr\u0005$\u0000\u0000qs\u0005\b\u0000\u0000"+
		"rq\u0001\u0000\u0000\u0000rs\u0001\u0000\u0000\u0000st\u0001\u0000\u0000"+
		"\u0000tu\u0005\u0004\u0000\u0000uv\u0005%\u0000\u0000v\u000f\u0001\u0000"+
		"\u0000\u0000w~\u0007\u0001\u0000\u0000x~\u0005\f\u0000\u0000y~\u0005\u000e"+
		"\u0000\u0000z~\u0005\r\u0000\u0000{~\u0005&\u0000\u0000|~\u0005(\u0000"+
		"\u0000}w\u0001\u0000\u0000\u0000}x\u0001\u0000\u0000\u0000}y\u0001\u0000"+
		"\u0000\u0000}z\u0001\u0000\u0000\u0000}{\u0001\u0000\u0000\u0000}|\u0001"+
		"\u0000\u0000\u0000~\u0011\u0001\u0000\u0000\u0000\u007f\u0080\u0005\n"+
		"\u0000\u0000\u0080\u0084\u0006\t\uffff\uffff\u0000\u0081\u0082\u0005\u0010"+
		"\u0000\u0000\u0082\u0084\u0006\t\uffff\uffff\u0000\u0083\u007f\u0001\u0000"+
		"\u0000\u0000\u0083\u0081\u0001\u0000\u0000\u0000\u0084\u0013\u0001\u0000"+
		"\u0000\u0000\u0011\u0017\u001c\"\',0=EGUZaemr}\u0083";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}