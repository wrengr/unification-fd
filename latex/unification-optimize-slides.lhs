% ***N.B. this uses PSTricks and so you need to use latex not pdflatex***
\documentclass[pdf,fyma2]{prosper} % Slide show (with "fyma2" style)
% The local fyma2 corrects some (new) alignment errors with the
% left side of the background gradation, the top and bottom lines,
% and the slide titles.
%
% Apparently prosper went obsolete when I wasn't looking. Powerdot
% looks like the non-obsolete successor to ha-prosper which is an
% (also obsolete) successor to prosper. Powerdot has a version of
% fyma, but it has the same alignment problem...
%
% fymafaintblue {0.88 0.95 1.00}
% fymalightblue {0.43 0.61 0.84} The bullets and lines
% fymablue      {0.24 0.45 0.70} The \ColorFoot (only marginally darker)
% fymadarkblue  {0.14 0.34 0.55} The regular text
% fymaroyalblue {0.06 0.25 0.41} The title text
\newgray{gris1}{.30}           % This was gris3 in rico/ricoDeux
\newgray{gris2}{.85}
\newrgbcolor{ocean}{0.00392156863 0.6 0.592156863}        % 0x01,99,97
\newrgbcolor{wine}{0.321568627 0.00392156863 0.333333333} % 0x52,01,55
% TODO: how to use \expandafter in order to redefine \emph?
\newcommand{\unhilight}[1]{{\color{gris2}#1}}
\newcommand{\hilighten}[1]{{\color{fymablue}#1}}

%\hypersetup{pdfpagemode=FullScreen} % make AcrobatReader auto full-screen
%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

% BUGFIX: this line fixes the erroneous "Error: Math version `bold'
% is not defined." error caused by packaging problems
\DeclareMathVersion{bold}
\usepackage{stmaryrd} % BUG: \llparenthesis\rrparenthesis has no displaystyle

\usepackage{amsmath,amssymb,latexsym}% defines \text{} in math mode
\usepackage{mathptmx} % mathtimes; BUG: may add serifs to other things...

\usepackage{pstricks,pst-node}
%\usepackage{graphicx}
%%\DeclareGraphicsExtensions{.pdf,.png,.jpg}
\usepackage{booktabs}


\newcommand{\opr}[1]{\ensuremath{\operatorname{#1}}}
\newcommand{\var}[1]{\ensuremath{\text{\textrm{\textit{#1}}}}}
\newcommand{\cat}[1]{\ensuremath{\mathbf{#1}}}

\newcommand{\BOOL}{\ensuremath{\mathbb{B}}}
\newcommand{\INT}{\ensuremath{\mathbb{Z}}}
\newcommand{\NAT}{\ensuremath{\mathbb{N}}}
\newcommand{\WHOLE}{\ensuremath{\mathbb{N}_{{>}0}}}
\newcommand{\SYM}[1][]{\ensuremath{\var{Sym}_{#1}}}
\newcommand{\ARITY}[1][]{\ensuremath{\var{Arity}_{#1}}}
\newcommand{\TERMS}[2][]{\ensuremath{\mathbb{T}_{#2}^{#1}}}
\newcommand{\FREEVARS}{\ensuremath{\var{FV}}}
\newcommand{\UNIFIERS}{\ensuremath{\mathcal{U}\!}}

\newcommand{\unify}{\ensuremath{\doteq}}
\newcommand{\isom}{\ensuremath{\cong}}
\newcommand{\notisom}{\ensuremath{\!\not{\!\!\isom\,}\,}}
\newcommand{\subsume}{\ensuremath{\lessdot}}
\newcommand{\subsumeq}{\ensuremath{\,\,\underline{\!\subsume\!}\,\,}}
\newcommand{\notsubsume}{\ensuremath{\!\not\!\!\subsume\,}}

% N.B., \it and \bf use serif fonts; whereas \textit, \textbf use sans-serif
\renewcommand{\emph}[1]{\hilighten{\textbf{#1}}}
\newcommand{\defn}[1]{\textbf{#1}}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%include polycode.fmt
%format (MT v t) = "\TERMS{" t "\uplus " v "}"
%format vv       = "\ensuremath{\mathcal{X}}"
%format tm       = "\ensuremath{\mathcal{F}}"
%format `eqVar`  = "\ensuremath{\equiv_{\null_V}}"
%format `acyclicBindVar` = "\ensuremath{:=_\Varid{acyc}}"

%format v0
%format v'
%format vInf = "\Varid{v}_\omega"
%format t0
%format t'
%format tInf = "\Varid{t}_\omega"
%format tl0
%format tl'
%format tr0
%format tr'
%format unify1
%format unify2
%format unify3
%format unify4
%format unify5

%format forall   = "\ensuremath{\forall}"
%format alpha    = "\ensuremath{\alpha}"
%format beta     = "\ensuremath{\beta}"

%format <$> = "\ensuremath{\odot}"
%format <*> = "\ensuremath{\circledast}"
%format <*  = "\ensuremath{\olessthan}"
%format  *> = "\ensuremath{\ogreaterthan}"
%format <|> = "\ensuremath{\obar}"

%format Int      = "\INT"
%format Integer  = "\INT"
%format Nat      = "\NAT"
%format Natural  = "\NAT"
%format Bool     = "\BOOL"

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

\title{Optimizing Unification}
\subtitle{from the ground up}
\date{7 July 2011}
\author{wren ng thornton}
\email{wrnthorn@@indiana.edu}
\institution{%
    Cognitive Science \& Computational Linguistics\\
    Indiana University Bloomington}
% N.B. entitlement.sty breaks prosper somehow...
\slideCaption{wren ng thornton \quad Optimizing Unification}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{document}

\maketitle

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Outline of the talk}
    \vspace{1em}
    \begin{itemize}
    \item The na{\"\i}ve approach
    \item Not quite so na{\"\i}ve: Cardelli (1987), a~la Sheard (2001)
        \begin{itemize}
        \item Implicit substitutions
        \item Full pruning: aka path compression
        \end{itemize}
    \item Semipruning
        \begin{itemize}
        \item Trivial observable sharing
        \item Enables future optimizations
        \end{itemize}
    \item Removing the occurs-check
    \item Aggressive opportunistic observable sharing
    \item Union--Find: aka weighted path compression
    \end{itemize}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{The na{\"\i}ve approach}
    \vspace{1em}
    \begin{itemize}
    \item Construct, compose, and apply substitutions per the definition
        \begin{itemize}
        \item This is \emph{eggregiously} inefficient
        \end{itemize}
    \vspace{1em}
    \item Not even worth pseudocode
        \begin{itemize}
        \item But Dijkstra, Middelkoop, \& Swierstra (2008) did it
        \end{itemize}
    \end{itemize}
    \vspace{-1.9em}
    \begin{center}
    \begin{tabular}{lrcrrcrrcrr}
    \toprule
    & &&
        \multicolumn{2}{c}{Na{\"\i}ve} &&
        \multicolumn{2}{c}{a~la Sheard} &&
        \multicolumn{2}{c}{w/o Occurs} \\
    \cmidrule(r){4-5}
    \cmidrule(r){7-8}
    \cmidrule(r){10-11}
    Test & Depth && sec & Mb && sec & Mb && sec & Mb \\
    \midrule
    linear
        &  500 && 0.67 &  61.7 && 0.52 & 2.9 && 0.04 & 2.8 \\
        & 1100 && 4.10 & 391.3 && 3.14 & 5.8 && 0.10 & 5.5 \\
        & 1600 && 8.60 & 687.5 && 7.67 & 7.5 && 0.14 & 7.4 \\
    \midrule
    exponential
        & 20 && 0.04 &   4.4 && 0.01 & 1.3 && 0.00 & 1.3 \\
        & 25 && 0.89 &  60.7 && 0.08 & 1.3 && 0.09 & 1.3 \\
        & 28 && 5.63 & 438.7 && 0.44 & 1.3 && 0.42 & 1.3 \\
    \bottomrule
    \end{tabular}
    \end{center}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Cardelli (1987), a~la Sheard (2001)}
    \vspace{1em}
    \begin{itemize}
    \item Two-level type of mutable terms
\begin{code}
data (MT) (vv :: * -> *) (tm :: * -> *) where
    MutVar   :: vv  ((MT vv tm)) -> MT vv tm
    MutTerm  :: tm  ((MT vv tm)) -> MT vv tm
\end{code}
    \item We assume the structural type implements |Traversable|
    \item And we assume the variable type implements
\begin{code}
class Variable vv where
    eqVar     :: vv alpha -> vv alpha -> Bool
    getVarID  :: vv alpha -> Int
\end{code}
    \item We will write |eqVar| infix as |(`eqVar`)|%'% Fix syntax hilighting
    \end{itemize}
\end{slide}

\begin{slide}{Cardelli (1987), a~la Sheard (2001)}
    \vspace{1em}
    \begin{itemize}
    \item Store substitutions in a monad
\begin{code}
class (...) => BindingMonad vv tm m where
    lookupVar  :: vv ((MT vv tm))               ->  m (Maybe (MT vv tm))
    freeVar    ::                                   m (vv ((MT vv tm)))
    newVar     ::                     MT vv tm  ->  m (vv ((MT vv tm)))
    bindVar    :: vv ((MT vv tm)) ->  MT vv tm  ->  m ()
\end{code}
    \item We will abbreviate |bindVar v t|, |lift (bindVar v t)|, etc, by |v := t|
% TODO: talk about the class constraints, and fundeps/assoctypes
% BUG: make {:=} look decent
    \end{itemize}
\end{slide}

\begin{slide}{Cardelli (1987), a~la Sheard (2001)}
    \vspace{1em}
    \begin{itemize}
    \item Full pruning: aka path compression
\begin{code}
prune (MutTerm  t0)  = return (MutTerm t0)
prune (MutVar   v0)  =
    case<- lookupVar v0 of
    Nothing  -> return (MutVar v0)
    Just t   -> do
        tInf  <- prune t
        v0    := tInf
        return tInf
\end{code}
    \end{itemize}
\end{slide}

\begin{slide}{Cardelli (1987), a~la Sheard (2001)}
    \vspace{1em}
    \begin{itemize}
    \item The occurs check
\begin{code}
occursIn v0 t0 =
    case<- prune t0 of
    MutTerm  t  -> or <$> mapM (v0 `occursIn`) t
    MutVar   v  -> return (v0 `eqVar` v)


acyclicBindVar v0 t0 =
    if<- lift (v0 `occursIn` t0)
    then  throwError (OccursIn v0 t0)
    else  v0 := t0
\end{code}
    \item We abbreviate |acyclicBindVar| infix as |`acyclicBindVar`|%'% Fix syntax hilighting
    \end{itemize}
\end{slide}

\begin{slide}{Cardelli (1987), a~la Sheard (2001)}
\begin{code}
unify1 tl0 tr0 = do
    tl <- lift (prune tl0)
    tr <- lift (prune tr0)
    case (tl, tr) of
    (MutVar  vl',    MutVar   vr'  )
        | vl' `eqVar` vr'             -> return ()
        | otherwise                   -> vl'  := tr
    (MutVar   vl',   MutTerm  _    )  -> vl'  `acyclicBindVar` tr
    (MutTerm  _,     MutVar   vr'  )  -> vr'  `acyclicBindVar` tl
    (MutTerm  tl',   MutTerm  tr'  )  -> 
        case match tl' tr' of
        Nothing     -> throwError (NonUnifiable tl tr)
        Just pairs  -> mapM_ (uncurry unify1) pairs
\end{code}
% TODO: describe match
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Optimization 1: Semipruning}
    \vspace{1em}
    \begin{itemize}
    \item Instead of pruning all the way to the last thing in the chain (i.e., term or free var), only prune to the last variable (whether bound or free)
    \vspace{1em}
    \item Trivial observable sharing
        \begin{itemize}
        \item In the Var--Var case,
            \begin{itemize}
            \item return immediately when bound vars are |eqVar|
            \item when the terms of bound vars unify, make them |eqVar|
            \end{itemize}
        \end{itemize}
    \item Enables future optimizations
        \begin{itemize}
        \item This is the kicker
        \end{itemize}
    \end{itemize}
\end{slide}
    
\begin{slide}{Optimization 1: Semipruning}
\begin{code}
semiprune (MutTerm  t0) = return (MutTerm t0)
semiprune (MutVar   v0) = loop v0
    where
    loop v =
        case<- lookupVar v of
        Nothing               -> return (MutVar v)
        Just (MutTerm  _   )  -> return (MutVar v)
        Just (MutVar   v'  )  -> do
            vInf  <- loop v'
            v     := MutVar vInf
            return (MutVar vInf)
\end{code}
\end{slide}
    
\begin{slide}{Optimization 1: Semipruning}
\vspace{-1.25em}
\begin{code}
unify2 tl0 tr0 = do
    tl <- lift (semiprune tl0)
    tr <- lift (semiprune tr0)
    case (tl, tr) of
    (MutVar   vl',  MutVar   vr'  )
        | vl' `eqVar` vr'             -> return () -- even if they're bound!
        | otherwise                   ->
            case<- lift ((,) <$> lookupVar vl' <*> lookupVar vr') of
            (Nothing,   Nothing    )  -> vl'  := tr
            (Nothing,   Just tr'   )  -> vl'  `acyclicBindVar` tr'
            (Just tl',  Nothing    )  -> vr'  `acyclicBindVar` tl'
            (Just tl',  Just tr'   )  -> do { unify2 tl' tr'; vl' := tr }
    (MutVar   vl',  MutTerm  _    )   -> ...
    (MutTerm  _,    MutVar   vr'  )   -> ...
    (MutTerm  tl',  MutTerm  tr'  )   -> ...
\end{code}
\end{slide}
\begin{slide}{Optimization 1: Semipruning}
\begin{code}
    ...
    (MutVar vl',   MutTerm _)    ->
        case<- lift (lookupVar vl') of
        Nothing   -> vl' `acyclicBindVar` tr
        Just tl'  -> unify2 tl' tr
    
    (MutTerm _,    MutVar vr')   ->
        case<- lift (lookupVar vr') of
        Nothing   -> vr' `acyclicBindVar` tl
        Just tr'  -> unify2 tl tr'
    
    (MutTerm tl',  MutTerm tr')  -> 
        case match tl' tr' of
        Nothing     -> throwError (NonUnifiable tl tr)
        Just pairs  -> mapM_ (uncurry unify2) pairs
\end{code}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Optimization 2: Removing the occurs-check}
    \vspace{1em}
    \begin{itemize}
    \item As we saw earlier, the occurs-check is expensive
    \item In fact, it's asymptotically bad
    \item Many versions of Prolog just remove it and allow cyclic terms to cause non-termination
    \item But there's a better way
        \begin{itemize}
        \item Keep track of the variables you've dereferenced
        \item Only complain when you try dereferencing it a second time
        \item Performance is approx $O(d*\log v)$ where $d$ is the depth of the term and $v$ is the number of variables seen ($v \leq d$)
        \end{itemize}
    \item Fails slow, but runs fast and avoids non-termination
        \begin{itemize}
        \item And we can cache the state of the first dereference for fails-fast quality error messages
        \end{itemize}
    \item But may fail too slow for some uses
        \begin{itemize}
        \item |unify x (f x)|
        \end{itemize}
    \end{itemize}
\end{slide}

% TODO: Figre out a |modify . insertWith| kind of thing
\begin{slide}{Optimization 2: Removing the occurs-check}
\begin{code}
v `seenAs` t = do
    seenVars <- get
    case IM.lookup (getVarID v) seenVars of
    Just t'  -> throwError (OccursIn v t')
    Nothing  -> put (IM.insert (getVarID v) t seenVars)
\end{code}
\end{slide}

\begin{slide}{Optimization 2: Removing the occurs-check}
\begin{code}
unify3 = \tl tr -> evalStateT (loop tl tr) IM.empty
    where
    loop tl0 tr0 = do
        tl   <- (lift . lift) (semiprune tl0)
        tr   <- (lift . lift) (semiprune tr0)
        case (tl, tr) of
        (MutVar  vl',   MutVar   vr'  ) -> ...
        (MutVar  vl',   MutTerm  _    ) ->
            case<- (lift . lift) (lookupVar vl') of
            Nothing   -> vl' := tr
            Just tl'  -> localState $ do { vl' `seenAs` tl'; loop tl' tr }
        (MutTerm  _,    MutVar   vr'  ) -> ... -- same as above
        (MutTerm  tl',  MutTerm  tr'  ) -> ... -- same as before
\end{code}
\end{slide}

\begin{slide}{Optimization 2: Removing the occurs-check}
\begin{code}
        ...
        (MutVar vl', MutVar vr')
            | vl' `eqVar` vr' -> return ()
            | otherwise       -> do
                case<- (lift . lift) ((,) <$> lookupVar vl' <*> lookupVar vr') of
                (Nothing,   Nothing   ) -> vl'  := tr
                (Nothing,   Just _    ) -> vl'  := tr
                (Just _,    Nothing   ) -> vr'  := tl
                (Just tl',  Just tr'  ) -> do
                    localState $ do
                        vl'  `seenAs` tl'
                        vr'  `seenAs` tr'
                        loop tl' tr'
                    vl' := tr
\end{code}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Optimization 3: AOOS}
    \vspace{1em}
    \begin{itemize}
    \item Semipruning gave us some opportunistic observable sharing
    \item What if we try to make aggressive use of it?
        \begin{itemize}
        \item Whenever unifying a variable, return that variable
        \item When returning from traversing a bound variable, rebind the variable to its new smaller term
        \end{itemize}
    \item To do this, we need to be able to traverse terms to rebuild them, not just fold over them.
        \begin{itemize}
        \item Replace |match :: tm alpha -> tm beta -> Maybe [(alpha,beta)]|
            \\ with |zipMatch :: tm alpha -> tm beta -> Maybe (tm (alpha,beta))|
        \end{itemize}
    \end{itemize}
\end{slide}

\begin{slide}{Optimization 3: AOOS}
    \vspace{1em}
    \begin{itemize}
    \item The beginning is the same as last time
    \end{itemize}
\begin{code}
unify4 = \tl tr -> evalStateT (loop tl tr) IM.empty
    where
    loop tl0 tr0 = do
        tl   <- (lift . lift) (semiprune tl0)
        tr   <- (lift . lift) (semiprune tr0)
        case (tl, tr) of
        ...
\end{code}
\end{slide}

\begin{slide}{Optimization 3: AOOS}
\begin{code}
        ...
        (MutVar vl', MutVar vr')
            | vl' `eqVar` vr'  -> return tr
            | otherwise        ->
                case<- (lift . lift) ((,) <$> lookupVar vl' <*> lookupVar vr') of
                (Nothing,   Nothing   ) -> do { vl'  := tr;  return tr }
                (Nothing,   Just _    ) -> do { vl'  := tr;  return tr }
                (Just _,    Nothing   ) -> do { vr'  := tl;  return tl }
                (Just tl',  Just tr'  ) -> do
                    t <- localState $ do { vl' `seenAs` tl'; vr' `seenAs` tr'; loop tl' tr' }
                    vr'  := t
                    vl'  := tr
                    return tr
        ...
\end{code}
\end{slide}

\begin{slide}{Optimization 3: AOOS}
\begin{code}
        ...
        (MutVar   vl',  MutTerm  _    ) -> do
            t <- do
                case<- (lift . lift) (lookupVar vl') of
                Nothing   -> return tr
                Just tl'  -> localState $ do { vl' `seenAs` tl'; loop tl' tr }
            vl' := t
            return tl
            
        (MutTerm  _,    MutVar   vr'  ) -> ...
            
        (MutTerm  tl',  MutTerm  tr'  ) ->
            case zipMatch tl' tr' of
            Nothing   -> throwError (NonUnifiable tl' tr')
            Just tlr  -> MutTerm <$> mapM (uncurry loop) tlr
\end{code}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{slide}{Optimization 4: Weighted path compression}
    \vspace{1em}
    \begin{itemize}
    \item In pathological cases, we could still build up long variable chains
        \begin{itemize}
        \item Up to $O(V * \log V)$ for a base access time of $O(\log V)$
        \item We'll only have to traverse it once (thanks to pruning),
        \item But can we do better?
        \end{itemize}
    \item Yes (asymptotically)
    \item Associate each variable with a mutable depth or `rank'
        \begin{itemize}
        \item When unifying variables to variables,
            \begin{itemize}
            \item bind the smaller variable to the larger
            \item if they're equal rank, then increment the target's rank by 1
            \end{itemize}
        \item Guarantees depth is bounded by $\log V$
        \end{itemize}
    \item Combining ranks+pruning yields $O(\alpha(V))$ amortized lookup time
        \begin{itemize}
        \item Times whatever the base access time is; e.g., $O(\log V)$
        \item This is asymptotically optimal
        \end{itemize}
    \item But the code gets a lot uglier--- beware constant factors
    \end{itemize}
\end{slide}

%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin.
% BUG: how can we use \pdfstringdef or \texorpdfstring to fix the PDF bookmark?
\part{%
\usefont{OT1}{ptm}{m}{it}\fontsize{14.4pt}{12pt}\selectfont
$\sim$fin.%
}
\end{document}
