use std::{
    fmt::{self, Write},
    mem::take,
};

use either::Either;
use hir::{known, HasVisibility, HirDisplay, HirWrite, ModuleDef, ModuleDefId, Semantics};
use ide_db::{base_db::FileRange, famous_defs::FamousDefs, RootDatabase};
use itertools::Itertools;
use stdx::never;
use syntax::{
    ast::{self, AstNode},
    match_ast, NodeOrToken, SyntaxNode, TextRange, TextSize,
};

use crate::{navigation_target::TryToNav, FileId};

mod closing_brace;
mod implicit_static;
mod fn_lifetime_fn;
mod closure_ret;
mod adjustment;
mod chaining;
mod param_name;
mod binding_mode;
mod bind_pat;
mod discriminant;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InlayHintsConfig {
    pub location_links: bool,
    pub render_colons: bool,
    pub type_hints: bool,
    pub discriminant_hints: DiscriminantHints,
    pub parameter_hints: bool,
    pub chaining_hints: bool,
    pub adjustment_hints: AdjustmentHints,
    pub adjustment_hints_mode: AdjustmentHintsMode,
    pub adjustment_hints_hide_outside_unsafe: bool,
    pub closure_return_type_hints: ClosureReturnTypeHints,
    pub binding_mode_hints: bool,
    pub lifetime_elision_hints: LifetimeElisionHints,
    pub param_names_for_lifetime_elision_hints: bool,
    pub hide_named_constructor_hints: bool,
    pub hide_closure_initialization_hints: bool,
    pub max_length: Option<usize>,
    pub closing_brace_hints_min_lines: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosureReturnTypeHints {
    Always,
    WithBlock,
    Never,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiscriminantHints {
    Always,
    Never,
    Fieldless,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LifetimeElisionHints {
    Always,
    SkipTrivial,
    Never,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdjustmentHints {
    Always,
    ReborrowOnly,
    Never,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AdjustmentHintsMode {
    Prefix,
    Postfix,
    PreferPrefix,
    PreferPostfix,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InlayKind {
    BindingModeHint,
    ChainingHint,
    ClosingBraceHint,
    ClosureReturnTypeHint,
    GenericParamListHint,
    AdjustmentHint,
    AdjustmentHintPostfix,
    LifetimeHint,
    ParameterHint,
    TypeHint,
    DiscriminantHint,
    OpeningParenthesis,
    ClosingParenthesis,
}

#[derive(Debug)]
pub struct InlayHint {
    pub range: TextRange,
    pub kind: InlayKind,
    pub label: InlayHintLabel,
    pub tooltip: Option<InlayTooltip>,
}

#[derive(Debug)]
pub enum InlayTooltip {
    String(String),
    HoverRanged(FileId, TextRange),
    HoverOffset(FileId, TextSize),
}

#[derive(Default)]
pub struct InlayHintLabel {
    pub parts: Vec<InlayHintLabelPart>,
}

impl InlayHintLabel {
    pub fn as_simple_str(&self) -> Option<&str> {
        match &*self.parts {
            [part] => part.as_simple_str(),
            _ => None,
        }
    }

    pub fn prepend_str(&mut self, s: &str) {
        match &mut *self.parts {
            [part, ..] if part.as_simple_str().is_some() => part.text = format!("{s}{}", part.text),
            _ => self.parts.insert(0, InlayHintLabelPart { text: s.into(), linked_location: None }),
        }
    }

    pub fn append_str(&mut self, s: &str) {
        match &mut *self.parts {
            [.., part] if part.as_simple_str().is_some() => part.text.push_str(s),
            _ => self.parts.push(InlayHintLabelPart { text: s.into(), linked_location: None }),
        }
    }
}

impl From<String> for InlayHintLabel {
    fn from(s: String) -> Self {
        Self { parts: vec![InlayHintLabelPart { text: s, linked_location: None }] }
    }
}

impl From<&str> for InlayHintLabel {
    fn from(s: &str) -> Self {
        Self { parts: vec![InlayHintLabelPart { text: s.into(), linked_location: None }] }
    }
}

impl fmt::Display for InlayHintLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.parts.iter().map(|part| &part.text).format(""))
    }
}

impl fmt::Debug for InlayHintLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.parts).finish()
    }
}

pub struct InlayHintLabelPart {
    pub text: String,
    /// Source location represented by this label part. The client will use this to fetch the part's
    /// hover tooltip, and Ctrl+Clicking the label part will navigate to the definition the location
    /// refers to (not necessarily the location itself).
    /// When setting this, no tooltip must be set on the containing hint, or VS Code will display
    /// them both.
    pub linked_location: Option<FileRange>,
}

impl InlayHintLabelPart {
    pub fn as_simple_str(&self) -> Option<&str> {
        match self {
            Self { text, linked_location: None } => Some(text),
            _ => None,
        }
    }
}

impl fmt::Debug for InlayHintLabelPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.as_simple_str() {
            Some(string) => string.fmt(f),
            None => f
                .debug_struct("InlayHintLabelPart")
                .field("text", &self.text)
                .field("linked_location", &self.linked_location)
                .finish(),
        }
    }
}

#[derive(Debug)]
struct InlayHintLabelBuilder<'a> {
    db: &'a RootDatabase,
    result: InlayHintLabel,
    last_part: String,
    location_link_enabled: bool,
    location: Option<FileRange>,
}

impl fmt::Write for InlayHintLabelBuilder<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.last_part.write_str(s)
    }
}

impl HirWrite for InlayHintLabelBuilder<'_> {
    fn start_location_link(&mut self, def: ModuleDefId) {
        if !self.location_link_enabled {
            return;
        }
        if self.location.is_some() {
            never!("location link is already started");
        }
        self.make_new_part();
        let Some(location) = ModuleDef::from(def).try_to_nav(self.db) else { return };
        let location =
            FileRange { file_id: location.file_id, range: location.focus_or_full_range() };
        self.location = Some(location);
    }

    fn end_location_link(&mut self) {
        if !self.location_link_enabled {
            return;
        }
        self.make_new_part();
    }
}

impl InlayHintLabelBuilder<'_> {
    fn make_new_part(&mut self) {
        self.result.parts.push(InlayHintLabelPart {
            text: take(&mut self.last_part),
            linked_location: self.location.take(),
        });
    }

    fn finish(mut self) -> InlayHintLabel {
        self.make_new_part();
        self.result
    }
}

fn label_of_ty(
    famous_defs @ FamousDefs(sema, _): &FamousDefs<'_, '_>,
    config: &InlayHintsConfig,
    ty: hir::Type,
) -> Option<InlayHintLabel> {
    fn rec(
        sema: &Semantics<'_, RootDatabase>,
        famous_defs: &FamousDefs<'_, '_>,
        mut max_length: Option<usize>,
        ty: hir::Type,
        label_builder: &mut InlayHintLabelBuilder<'_>,
    ) {
        let iter_item_type = hint_iterator(sema, famous_defs, &ty);
        match iter_item_type {
            Some(ty) => {
                const LABEL_START: &str = "impl Iterator<Item = ";
                const LABEL_END: &str = ">";

                max_length =
                    max_length.map(|len| len.saturating_sub(LABEL_START.len() + LABEL_END.len()));

                label_builder.write_str(LABEL_START).unwrap();
                rec(sema, famous_defs, max_length, ty, label_builder);
                label_builder.write_str(LABEL_END).unwrap();
            }
            None => {
                let _ = ty.display_truncated(sema.db, max_length).write_to(label_builder);
            }
        };
    }

    let mut label_builder = InlayHintLabelBuilder {
        db: sema.db,
        last_part: String::new(),
        location: None,
        location_link_enabled: config.location_links,
        result: InlayHintLabel::default(),
    };
    rec(sema, famous_defs, config.max_length, ty, &mut label_builder);
    let r = label_builder.finish();
    Some(r)
}

// Feature: Inlay Hints
//
// rust-analyzer shows additional information inline with the source code.
// Editors usually render this using read-only virtual text snippets interspersed with code.
//
// rust-analyzer by default shows hints for
//
// * types of local variables
// * names of function arguments
// * types of chained expressions
//
// Optionally, one can enable additional hints for
//
// * return types of closure expressions
// * elided lifetimes
// * compiler inserted reborrows
//
// image::https://user-images.githubusercontent.com/48062697/113020660-b5f98b80-917a-11eb-8d70-3be3fd558cdd.png[]
pub(crate) fn inlay_hints(
    db: &RootDatabase,
    file_id: FileId,
    range_limit: Option<TextRange>,
    config: &InlayHintsConfig,
) -> Vec<InlayHint> {
    let _p = profile::span("inlay_hints");
    let sema = Semantics::new(db);
    let file = sema.parse(file_id);
    let file = file.syntax();

    let mut acc = Vec::new();

    if let Some(scope) = sema.scope(file) {
        let famous_defs = FamousDefs(&sema, scope.krate());

        let hints = |node| hints(&mut acc, &famous_defs, config, file_id, node);
        match range_limit {
            Some(range) => match file.covering_element(range) {
                NodeOrToken::Token(_) => return acc,
                NodeOrToken::Node(n) => n
                    .descendants()
                    .filter(|descendant| range.intersect(descendant.text_range()).is_some())
                    .for_each(hints),
            },
            None => file.descendants().for_each(hints),
        };
    }

    acc
}

fn hints(
    hints: &mut Vec<InlayHint>,
    famous_defs @ FamousDefs(sema, _): &FamousDefs<'_, '_>,
    config: &InlayHintsConfig,
    file_id: FileId,
    node: SyntaxNode,
) {
    closing_brace::hints(hints, sema, config, file_id, node.clone());
    match_ast! {
        match node {
            ast::Expr(expr) => {
                chaining::hints(hints, famous_defs, config, file_id, &expr);
                adjustment::hints(hints, sema, config, &expr);
                match expr {
                    ast::Expr::CallExpr(it) => param_name::hints(hints, sema, config, ast::Expr::from(it)),
                    ast::Expr::MethodCallExpr(it) => {
                        param_name::hints(hints, sema, config, ast::Expr::from(it))
                    }
                    ast::Expr::ClosureExpr(it) => closure_ret::hints(hints, famous_defs, config, file_id, it),
                    // We could show reborrows for all expressions, but usually that is just noise to the user
                    // and the main point here is to show why "moving" a mutable reference doesn't necessarily move it
                    // ast::Expr::PathExpr(_) => reborrow_hints(hints, sema, config, &expr),
                    _ => None,
                }
            },
            ast::Pat(it) => {
                binding_mode::hints(hints, sema, config, &it);
                if let ast::Pat::IdentPat(it) = it {
                    bind_pat::hints(hints, famous_defs, config, file_id, &it);
                }
                Some(())
            },
            ast::Item(it) => match it {
                // FIXME: record impl lifetimes so they aren't being reused in assoc item lifetime inlay hints
                ast::Item::Impl(_) => None,
                ast::Item::Fn(it) => fn_lifetime_fn::hints(hints, config, it),
                // static type elisions
                ast::Item::Static(it) => implicit_static::hints(hints, config, Either::Left(it)),
                ast::Item::Const(it) => implicit_static::hints(hints, config, Either::Right(it)),
                _ => None,
            },
            ast::Variant(v) => {
                discriminant::hints(hints, famous_defs, config, file_id, &v)
            },
            // FIXME: fn-ptr type, dyn fn type, and trait object type elisions
            ast::Type(_) => None,
            _ => None,
        }
    };
}

fn closing_brace_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    file_id: FileId,
    node: SyntaxNode,
) -> Option<()> {
    let min_lines = config.closing_brace_hints_min_lines?;

    let name = |it: ast::Name| it.syntax().text_range();

    let mut closing_token;
    let (label, name_range) = if let Some(item_list) = ast::AssocItemList::cast(node.clone()) {
        closing_token = item_list.r_curly_token()?;

        let parent = item_list.syntax().parent()?;
        match_ast! {
            match parent {
                ast::Impl(imp) => {
                    let imp = sema.to_def(&imp)?;
                    let ty = imp.self_ty(sema.db);
                    let trait_ = imp.trait_(sema.db);
                    let hint_text = match trait_ {
                        Some(tr) => format!("impl {} for {}", tr.name(sema.db), ty.display_truncated(sema.db, config.max_length)),
                        None => format!("impl {}", ty.display_truncated(sema.db, config.max_length)),
                    };
                    (hint_text, None)
                },
                ast::Trait(tr) => 
                    (format!("trait {}", tr.name()?), tr.name().map(name)),
                _ => return None,
            }
        }
    } else if let Some(list) = ast::ItemList::cast(node.clone()) {
        closing_token = list.r_curly_token()?;

        let module = ast::Module::cast(list.syntax().parent()?)?;
        (format!("mod {}", module.name()?), module.name().map(name))
    } else if let Some(block) = ast::BlockExpr::cast(node.clone()) {
        closing_token = block.stmt_list()?.r_curly_token()?;

        let parent = block.syntax().parent()?;
        match_ast! {
            match parent {
                ast::Fn(it) =>
                    // FIXME: this could include parameters, but `HirDisplay` prints too much info
                    // and doesn't respect the max length either, so the hints end up way too long
                    (format!("fn {}", it.name()?), it.name().map(name)),
                ast::Static(it) => (format!("static {}", it.name()?), it.name().map(name)),
                ast::Const(it) => 
                    if it.underscore_token().is_some() {
                        ("const _".into(), None)
                    } else {
                        (format!("const {}", it.name()?), it.name().map(name))
                    },
                _ => return None,
            }
        }
    } else if let Some(mac) = ast::MacroCall::cast(node.clone()) {
        let last_token = mac.syntax().last_token()?;
        if last_token.kind() != T![;] && last_token.kind() != SyntaxKind::R_CURLY {
            return None;
        }
        closing_token = last_token;

        (
            format!("{}!", mac.path()?),
            mac.path().and_then(|it| it.segment()).map(|it| it.syntax().text_range()),
        )
    } else {
        return None;
    };

    if let Some(mut next) = closing_token.next_token() {
        if next.kind() == T![;] {
            if let Some(tok) = next.next_token() {
                closing_token = next;
                next = tok;
            }
        }
        if !(next.kind() == SyntaxKind::WHITESPACE && next.text().contains('\n')) {
            // Only display the hint if the `}` is the last token on the line
            return None;
        }
    }

    let mut lines = 1;
    node.text().for_each_chunk(|s| lines += s.matches('\n').count());
    if lines < min_lines {
        return None;
    }

    let linked_location = name_range.map(|range| FileRange { file_id, range });
    acc.push(InlayHint {
        range: closing_token.text_range(),
        kind: InlayKind::ClosingBraceHint,
        label: InlayHintLabel { parts: vec![InlayHintLabelPart { text: label, linked_location }] },
        tooltip: None, // provided by label part location
    });

    None
}

fn implicit_static_hints(
    acc: &mut Vec<InlayHint>,
    config: &InlayHintsConfig,
    statik_or_const: Either<ast::Static, ast::Const>,
) -> Option<()> {
    if config.lifetime_elision_hints != LifetimeElisionHints::Always {
        return None;
    }

    if let Either::Right(it) = &statik_or_const {
        if ast::AssocItemList::can_cast(
            it.syntax().parent().map_or(SyntaxKind::EOF, |it| it.kind()),
        ) {
            return None;
        }
    }

    if let Some(ast::Type::RefType(ty)) = statik_or_const.either(|it| it.ty(), |it| it.ty()) {
        if ty.lifetime().is_none() {
            let t = ty.amp_token()?;
            acc.push(InlayHint {
                range: t.text_range(),
                kind: InlayKind::LifetimeHint,
                label: "'static".to_owned().into(),
                tooltip: Some(InlayTooltip::String("Elided static lifetime".into())),
            });
        }
    }

    Some(())
}

fn fn_lifetime_fn_hints(
    acc: &mut Vec<InlayHint>,
    config: &InlayHintsConfig,
    func: ast::Fn,
) -> Option<()> {
    if config.lifetime_elision_hints == LifetimeElisionHints::Never {
        return None;
    }

    let mk_lt_hint = |t: SyntaxToken, label: String| InlayHint {
        range: t.text_range(),
        kind: InlayKind::LifetimeHint,
        label: label.into(),
        tooltip: Some(InlayTooltip::String("Elided lifetime".into())),
    };

    let param_list = func.param_list()?;
    let generic_param_list = func.generic_param_list();
    let ret_type = func.ret_type();
    let self_param = param_list.self_param().filter(|it| it.amp_token().is_some());

    let is_elided = |lt: &Option<ast::Lifetime>| match lt {
        Some(lt) => matches!(lt.text().as_str(), "'_"),
        None => true,
    };

    let potential_lt_refs = {
        let mut acc: Vec<_> = vec![];
        if let Some(self_param) = &self_param {
            let lifetime = self_param.lifetime();
            let is_elided = is_elided(&lifetime);
            acc.push((None, self_param.amp_token(), lifetime, is_elided));
        }
        param_list.params().filter_map(|it| Some((it.pat(), it.ty()?))).for_each(|(pat, ty)| {
            // FIXME: check path types
            walk_ty(&ty, &mut |ty| match ty {
                ast::Type::RefType(r) => {
                    let lifetime = r.lifetime();
                    let is_elided = is_elided(&lifetime);
                    acc.push((
                        pat.as_ref().and_then(|it| match it {
                            ast::Pat::IdentPat(p) => p.name(),
                            _ => None,
                        }),
                        r.amp_token(),
                        lifetime,
                        is_elided,
                    ))
                }
                _ => (),
            })
        });
        acc
    };

    // allocate names
    let mut gen_idx_name = {
        let mut gen = (0u8..).map(|idx| match idx {
            idx if idx < 10 => SmolStr::from_iter(['\'', (idx + 48) as char]),
            idx => format!("'{idx}").into(),
        });
        move || gen.next().unwrap_or_default()
    };
    let mut allocated_lifetimes = vec![];

    let mut used_names: FxHashMap<SmolStr, usize> =
        match config.param_names_for_lifetime_elision_hints {
            true => generic_param_list
                .iter()
                .flat_map(|gpl| gpl.lifetime_params())
                .filter_map(|param| param.lifetime())
                .filter_map(|lt| Some((SmolStr::from(lt.text().as_str().get(1..)?), 0)))
                .collect(),
            false => Default::default(),
        };
    {
        let mut potential_lt_refs = potential_lt_refs.iter().filter(|&&(.., is_elided)| is_elided);
        if let Some(_) = &self_param {
            if let Some(_) = potential_lt_refs.next() {
                allocated_lifetimes.push(if config.param_names_for_lifetime_elision_hints {
                    // self can't be used as a lifetime, so no need to check for collisions
                    "'self".into()
                } else {
                    gen_idx_name()
                });
            }
        }
        potential_lt_refs.for_each(|(name, ..)| {
            let name = match name {
                Some(it) if config.param_names_for_lifetime_elision_hints => {
                    if let Some(c) = used_names.get_mut(it.text().as_str()) {
                        *c += 1;
                        SmolStr::from(format!("'{text}{c}", text = it.text().as_str()))
                    } else {
                        used_names.insert(it.text().as_str().into(), 0);
                        SmolStr::from_iter(["\'", it.text().as_str()])
                    }
                }
                _ => gen_idx_name(),
            };
            allocated_lifetimes.push(name);
        });
    }

    // fetch output lifetime if elision rule applies
    let output = match potential_lt_refs.as_slice() {
        [(_, _, lifetime, _), ..] if self_param.is_some() || potential_lt_refs.len() == 1 => {
            match lifetime {
                Some(lt) => match lt.text().as_str() {
                    "'_" => allocated_lifetimes.get(0).cloned(),
                    "'static" => None,
                    name => Some(name.into()),
                },
                None => allocated_lifetimes.get(0).cloned(),
            }
        }
        [..] => None,
    };

    if allocated_lifetimes.is_empty() && output.is_none() {
        return None;
    }

    // apply hints
    // apply output if required
    let mut is_trivial = true;
    if let (Some(output_lt), Some(r)) = (&output, ret_type) {
        if let Some(ty) = r.ty() {
            walk_ty(&ty, &mut |ty| match ty {
                ast::Type::RefType(ty) if ty.lifetime().is_none() => {
                    if let Some(amp) = ty.amp_token() {
                        is_trivial = false;
                        acc.push(mk_lt_hint(amp, output_lt.to_string()));
                    }
                }
                _ => (),
            })
        }
    }

    if config.lifetime_elision_hints == LifetimeElisionHints::SkipTrivial && is_trivial {
        return None;
    }

    let mut a = allocated_lifetimes.iter();
    for (_, amp_token, _, is_elided) in potential_lt_refs {
        if is_elided {
            let t = amp_token?;
            let lt = a.next()?;
            acc.push(mk_lt_hint(t, lt.to_string()));
        }
    }

    // generate generic param list things
    match (generic_param_list, allocated_lifetimes.as_slice()) {
        (_, []) => (),
        (Some(gpl), allocated_lifetimes) => {
            let angle_tok = gpl.l_angle_token()?;
            let is_empty = gpl.generic_params().next().is_none();
            acc.push(InlayHint {
                range: angle_tok.text_range(),
                kind: InlayKind::LifetimeHint,
                label: format!(
                    "{}{}",
                    allocated_lifetimes.iter().format(", "),
                    if is_empty { "" } else { ", " }
                )
                .into(),
                tooltip: Some(InlayTooltip::String("Elided lifetimes".into())),
            });
        }
        (None, allocated_lifetimes) => acc.push(InlayHint {
            range: func.name()?.syntax().text_range(),
            kind: InlayKind::GenericParamListHint,
            label: format!("<{}>", allocated_lifetimes.iter().format(", "),).into(),
            tooltip: Some(InlayTooltip::String("Elided lifetimes".into())),
        }),
    }
    Some(())
}

fn closure_ret_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    famous_defs: &FamousDefs<'_, '_>,
    config: &InlayHintsConfig,
    file_id: FileId,
    closure: ast::ClosureExpr,
) -> Option<()> {
    if config.closure_return_type_hints == ClosureReturnTypeHints::Never {
        return None;
    }

    if closure.ret_type().is_some() {
        return None;
    }

    if !closure_has_block_body(&closure)
        && config.closure_return_type_hints == ClosureReturnTypeHints::WithBlock
    {
        return None;
    }

    let param_list = closure.param_list()?;

    let closure = sema.descend_node_into_attributes(closure.clone()).pop()?;
    let ty = sema.type_of_expr(&ast::Expr::ClosureExpr(closure))?.adjusted();
    let callable = ty.as_callable(sema.db)?;
    let ty = callable.return_type();
    if ty.is_unit() {
        return None;
    }
    acc.push(InlayHint {
        range: param_list.syntax().text_range(),
        kind: InlayKind::ClosureReturnTypeHint,
        label: hint_iterator(sema, &famous_defs, config, &ty)
            .unwrap_or_else(|| ty.display_truncated(sema.db, config.max_length).to_string())
            .into(),
        tooltip: Some(InlayTooltip::HoverRanged(file_id, param_list.syntax().text_range())),
    });
    Some(())
}

fn adjustment_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    expr: &ast::Expr,
) -> Option<()> {
    if config.adjustment_hints == AdjustmentHints::Never {
        return None;
    }

    if let ast::Expr::ParenExpr(_) = expr {
        // These inherit from the inner expression which would result in duplicate hints
        return None;
    }

    let parent = expr.syntax().parent().and_then(ast::Expr::cast);
    let descended = sema.descend_node_into_attributes(expr.clone()).pop();
    let desc_expr = descended.as_ref().unwrap_or(expr);
    let adjustments = sema.expr_adjustments(desc_expr).filter(|it| !it.is_empty())?;
    let needs_parens = match parent {
        Some(parent) => {
            match parent {
                ast::Expr::AwaitExpr(_)
                | ast::Expr::CallExpr(_)
                | ast::Expr::CastExpr(_)
                | ast::Expr::FieldExpr(_)
                | ast::Expr::MethodCallExpr(_)
                | ast::Expr::TryExpr(_) => true,
                // FIXME: shorthands need special casing, though not sure if adjustments are even valid there
                ast::Expr::RecordExpr(_) => false,
                ast::Expr::IndexExpr(index) => index.base().as_ref() == Some(expr),
                _ => false,
            }
        }
        None => false,
    };
    if needs_parens {
        acc.push(InlayHint {
            range: expr.syntax().text_range(),
            kind: InlayKind::AdjustmentHint,
            label: "(".into(),
            tooltip: None,
        });
    }
    for adjustment in adjustments.into_iter().rev() {
        // FIXME: Add some nicer tooltips to each of these
        let text = match adjustment {
            Adjust::NeverToAny if config.adjustment_hints == AdjustmentHints::Always => {
                "<never-to-any>"
            }
            Adjust::Deref(None) => "*",
            Adjust::Deref(Some(OverloadedDeref(Mutability::Mut))) => "*",
            Adjust::Deref(Some(OverloadedDeref(Mutability::Shared))) => "*",
            Adjust::Borrow(AutoBorrow::Ref(Mutability::Shared)) => "&",
            Adjust::Borrow(AutoBorrow::Ref(Mutability::Mut)) => "&mut ",
            Adjust::Borrow(AutoBorrow::RawPtr(Mutability::Shared)) => "&raw const ",
            Adjust::Borrow(AutoBorrow::RawPtr(Mutability::Mut)) => "&raw mut ",
            // some of these could be represented via `as` casts, but that's not too nice and
            // handling everything as a prefix expr makes the `(` and `)` insertion easier
            Adjust::Pointer(cast) if config.adjustment_hints == AdjustmentHints::Always => {
                match cast {
                    PointerCast::ReifyFnPointer => "<fn-item-to-fn-pointer>",
                    PointerCast::UnsafeFnPointer => "<safe-fn-pointer-to-unsafe-fn-pointer>",
                    PointerCast::ClosureFnPointer(Safety::Unsafe) => {
                        "<closure-to-unsafe-fn-pointer>"
                    }
                    PointerCast::ClosureFnPointer(Safety::Safe) => "<closure-to-fn-pointer>",
                    PointerCast::MutToConstPointer => "<mut-ptr-to-const-ptr>",
                    PointerCast::ArrayToPointer => "<array-ptr-to-element-ptr>",
                    PointerCast::Unsize => "<unsize>",
                }
            }
            _ => continue,
        };
        acc.push(InlayHint {
            range: expr.syntax().text_range(),
            kind: InlayKind::AdjustmentHint,
            label: text.into(),
            tooltip: None,
        });
    }
    if needs_parens {
        acc.push(InlayHint {
            range: expr.syntax().text_range(),
            kind: InlayKind::AdjustmentHintClosingParenthesis,
            label: ")".into(),
            tooltip: None,
        });
    }
    Some(())
}

fn chaining_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    famous_defs: &FamousDefs<'_, '_>,
    config: &InlayHintsConfig,
    file_id: FileId,
    expr: &ast::Expr,
) -> Option<()> {
    if !config.chaining_hints {
        return None;
    }

    if matches!(expr, ast::Expr::RecordExpr(_)) {
        return None;
    }

    let descended = sema.descend_node_into_attributes(expr.clone()).pop();
    let desc_expr = descended.as_ref().unwrap_or(expr);

    let mut tokens = expr
        .syntax()
        .siblings_with_tokens(Direction::Next)
        .filter_map(NodeOrToken::into_token)
        .filter(|t| match t.kind() {
            SyntaxKind::WHITESPACE if !t.text().contains('\n') => false,
            SyntaxKind::COMMENT => false,
            _ => true,
        });

    // Chaining can be defined as an expression whose next sibling tokens are newline and dot
    // Ignoring extra whitespace and comments
    let next = tokens.next()?.kind();
    if next == SyntaxKind::WHITESPACE {
        let mut next_next = tokens.next()?.kind();
        while next_next == SyntaxKind::WHITESPACE {
            next_next = tokens.next()?.kind();
        }
        if next_next == T![.] {
            let ty = sema.type_of_expr(desc_expr)?.original;
            if ty.is_unknown() {
                return None;
            }
            if matches!(expr, ast::Expr::PathExpr(_)) {
                if let Some(hir::Adt::Struct(st)) = ty.as_adt() {
                    if st.fields(sema.db).is_empty() {
                        return None;
                    }
                }
            }
            acc.push(InlayHint {
                range: expr.syntax().text_range(),
                kind: InlayKind::ChainingHint,
                label: hint_iterator(sema, &famous_defs, config, &ty)
                    .unwrap_or_else(|| ty.display_truncated(sema.db, config.max_length).to_string())
                    .into(),
                tooltip: Some(InlayTooltip::HoverRanged(file_id, expr.syntax().text_range())),
            });
        }
    }
    Some(())
}

fn param_name_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    expr: ast::Expr,
) -> Option<()> {
    if !config.parameter_hints {
        return None;
    }

    let (callable, arg_list) = get_callable(sema, &expr)?;
    let hints = callable
        .params(sema.db)
        .into_iter()
        .zip(arg_list.args())
        .filter_map(|((param, _ty), arg)| {
            // Only annotate hints for expressions that exist in the original file
            let range = sema.original_range_opt(arg.syntax())?;
            let (param_name, name_syntax) = match param.as_ref()? {
                Either::Left(pat) => ("self".to_string(), pat.name()),
                Either::Right(pat) => match pat {
                    ast::Pat::IdentPat(it) => (it.name()?.to_string(), it.name()),
                    _ => return None,
                },
            };
            Some((name_syntax, param_name, arg, range))
        })
        .filter(|(_, param_name, arg, _)| {
            !should_hide_param_name_hint(sema, &callable, param_name, arg)
        })
        .map(|(param, param_name, _, FileRange { range, .. })| {
            let mut tooltip = None;
            if let Some(name) = param {
                if let hir::CallableKind::Function(f) = callable.kind() {
                    // assert the file is cached so we can map out of macros
                    if let Some(_) = sema.source(f) {
                        tooltip = sema.original_range_opt(name.syntax());
                    }
                }
            }

            InlayHint {
                range,
                kind: InlayKind::ParameterHint,
                label: param_name.into(),
                tooltip: tooltip.map(|it| InlayTooltip::HoverOffset(it.file_id, it.range.start())),
            }
        });

    acc.extend(hints);
    Some(())
}

fn binding_mode_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    pat: &ast::Pat,
) -> Option<()> {
    if !config.binding_mode_hints {
        return None;
    }

    let range = pat.syntax().text_range();
    sema.pattern_adjustments(&pat).iter().for_each(|ty| {
        let reference = ty.is_reference();
        let mut_reference = ty.is_mutable_reference();
        let r = match (reference, mut_reference) {
            (true, true) => "&mut",
            (true, false) => "&",
            _ => return,
        };
        acc.push(InlayHint {
            range,
            kind: InlayKind::BindingModeHint,
            label: r.to_string().into(),
            tooltip: Some(InlayTooltip::String("Inferred binding mode".into())),
        });
    });
    match pat {
        ast::Pat::IdentPat(pat) if pat.ref_token().is_none() && pat.mut_token().is_none() => {
            let bm = sema.binding_mode_of_pat(pat)?;
            let bm = match bm {
                hir::BindingMode::Move => return None,
                hir::BindingMode::Ref(Mutability::Mut) => "ref mut",
                hir::BindingMode::Ref(Mutability::Shared) => "ref",
            };
            acc.push(InlayHint {
                range,
                kind: InlayKind::BindingModeHint,
                label: bm.to_string().into(),
                tooltip: Some(InlayTooltip::String("Inferred binding mode".into())),
            });
        }
        _ => (),
    }

    Some(())
}

fn bind_pat_hints(
    acc: &mut Vec<InlayHint>,
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    file_id: FileId,
    pat: &ast::IdentPat,
) -> Option<()> {
    if !config.type_hints {
        return None;
    }

    let descended = sema.descend_node_into_attributes(pat.clone()).pop();
    let desc_pat = descended.as_ref().unwrap_or(pat);
    let ty = sema.type_of_pat(&desc_pat.clone().into())?.original;

    if should_not_display_type_hint(sema, config, pat, &ty) {
        return None;
    }

    let krate = sema.scope(desc_pat.syntax())?.krate();
    let famous_defs = FamousDefs(sema, krate);
    let label = hint_iterator(sema, &famous_defs, config, &ty);

    let label = match label {
        Some(label) => label,
        None => {
            let ty_name = ty.display_truncated(sema.db, config.max_length).to_string();
            if config.hide_named_constructor_hints
                && is_named_constructor(sema, pat, &ty_name).is_some()
            {
                return None;
            }
            ty_name
        }
    };

    acc.push(InlayHint {
        range: match pat.name() {
            Some(name) => name.syntax().text_range(),
            None => pat.syntax().text_range(),
        },
        kind: InlayKind::TypeHint,
        label: label.into(),
        tooltip: pat
            .name()
            .map(|it| it.syntax().text_range())
            .map(|it| InlayTooltip::HoverRanged(file_id, it)),
    });

    Some(())
}

fn is_named_constructor(
    sema: &Semantics<'_, RootDatabase>,
    pat: &ast::IdentPat,
    ty_name: &str,
) -> Option<()> {
    let let_node = pat.syntax().parent()?;
    let expr = match_ast! {
        match let_node {
            ast::LetStmt(it) => it.initializer(),
            ast::LetExpr(it) => it.expr(),
            _ => None,
        }
    }?;

    let expr = sema.descend_node_into_attributes(expr.clone()).pop().unwrap_or(expr);
    // unwrap postfix expressions
    let expr = match expr {
        ast::Expr::TryExpr(it) => it.expr(),
        ast::Expr::AwaitExpr(it) => it.expr(),
        expr => Some(expr),
    }?;
    let expr = match expr {
        ast::Expr::CallExpr(call) => match call.expr()? {
            ast::Expr::PathExpr(path) => path,
            _ => return None,
        },
        ast::Expr::PathExpr(path) => path,
        _ => return None,
    };
    let path = expr.path()?;

    let callable = sema.type_of_expr(&ast::Expr::PathExpr(expr))?.original.as_callable(sema.db);
    let callable_kind = callable.map(|it| it.kind());
    let qual_seg = match callable_kind {
        Some(hir::CallableKind::Function(_) | hir::CallableKind::TupleEnumVariant(_)) => {
            path.qualifier()?.segment()
        }
        _ => path.segment(),
    }?;

    let ctor_name = match qual_seg.kind()? {
        ast::PathSegmentKind::Name(name_ref) => {
            match qual_seg.generic_arg_list().map(|it| it.generic_args()) {
                Some(generics) => format!("{}<{}>", name_ref, generics.format(", ")),
                None => name_ref.to_string(),
            }
        }
        ast::PathSegmentKind::Type { type_ref: Some(ty), trait_ref: None } => ty.to_string(),
        _ => return None,
    };
    (ctor_name == ty_name).then(|| ())
}

/// Checks if the type is an Iterator from std::iter and replaces its hint with an `impl Iterator<Item = Ty>`.
fn hint_iterator(
    sema: &Semantics<'_, RootDatabase>,
    famous_defs: &FamousDefs<'_, '_>,
    ty: &hir::Type,
) -> Option<hir::Type> {
    let db = sema.db;
    let strukt = ty.strip_references().as_adt()?;
    let krate = strukt.module(db).krate();
    if krate != famous_defs.core()? {
        return None;
    }
    let iter_trait = famous_defs.core_iter_Iterator()?;
    let iter_mod = famous_defs.core_iter()?;

    // Assert that this struct comes from `core::iter`.
    if !(strukt.visibility(db) == hir::Visibility::Public
        && strukt.module(db).path_to_root(db).contains(&iter_mod))
    {
        return None;
    }

    if ty.impls_trait(db, iter_trait, &[]) {
        let assoc_type_item = iter_trait.items(db).into_iter().find_map(|item| match item {
            hir::AssocItem::TypeAlias(alias) if alias.name(db) == known::Item => Some(alias),
            _ => None,
        })?;
        if let Some(ty) = ty.normalize_trait_assoc_type(db, &[], assoc_type_item) {
            return Some(ty);
        }
    }

    None
}

fn pat_is_enum_variant(db: &RootDatabase, bind_pat: &ast::IdentPat, pat_ty: &hir::Type) -> bool {
    if let Some(hir::Adt::Enum(enum_data)) = pat_ty.as_adt() {
        let pat_text = bind_pat.to_string();
        enum_data
            .variants(db)
            .into_iter()
            .map(|variant| variant.name(db).to_smol_str())
            .any(|enum_name| enum_name == pat_text)
    } else {
        false
    }
}

fn should_not_display_type_hint(
    sema: &Semantics<'_, RootDatabase>,
    config: &InlayHintsConfig,
    bind_pat: &ast::IdentPat,
    pat_ty: &hir::Type,
) -> bool {
    let db = sema.db;

    if pat_ty.is_unknown() {
        return true;
    }

    if let Some(hir::Adt::Struct(s)) = pat_ty.as_adt() {
        if s.fields(db).is_empty() && s.name(db).to_smol_str() == bind_pat.to_string() {
            return true;
        }
    }

    if config.hide_closure_initialization_hints {
        if let Some(parent) = bind_pat.syntax().parent() {
            if let Some(it) = ast::LetStmt::cast(parent.clone()) {
                if let Some(ast::Expr::ClosureExpr(closure)) = it.initializer() {
                    if closure_has_block_body(&closure) {
                        return true;
                    }
                }
            }
        }
    }

    for node in bind_pat.syntax().ancestors() {
        match_ast! {
            match node {
                ast::LetStmt(it) => return it.ty().is_some(),
                // FIXME: We might wanna show type hints in parameters for non-top level patterns as well
                ast::Param(it) => return it.ty().is_some(),
                ast::MatchArm(_) => return pat_is_enum_variant(db, bind_pat, pat_ty),
                ast::LetExpr(_) => return pat_is_enum_variant(db, bind_pat, pat_ty),
                ast::IfExpr(_) => return false,
                ast::WhileExpr(_) => return false,
                ast::ForExpr(it) => 
                    // We *should* display hint only if user provided "in {expr}" and we know the type of expr (and it's not unit).
                    // Type of expr should be iterable.
                    return it.in_token().is_none() ||
                        it.iterable()
                            .and_then(|iterable_expr| sema.type_of_expr(&iterable_expr))
                            .map(TypeInfo::original)
                            .map_or(true, |iterable_ty| iterable_ty.is_unknown() || iterable_ty.is_unit()),
                _ => (),
            }
        }
    }
    false
}

fn closure_has_block_body(closure: &ast::ClosureExpr) -> bool {
    matches!(closure.body(), Some(ast::Expr::BlockExpr(_)))
}

#[cfg(test)]
mod tests {
    use expect_test::Expect;
    use itertools::Itertools;
    use test_utils::extract_annotations;

    use crate::inlay_hints::{AdjustmentHints, AdjustmentHintsMode};
    use crate::DiscriminantHints;
    use crate::{fixture, inlay_hints::InlayHintsConfig, LifetimeElisionHints};

    use super::ClosureReturnTypeHints;

    pub(super) const DISABLED_CONFIG: InlayHintsConfig = InlayHintsConfig {
        location_links: false,
        discriminant_hints: DiscriminantHints::Never,
        render_colons: false,
        type_hints: false,
        parameter_hints: false,
        chaining_hints: false,
        lifetime_elision_hints: LifetimeElisionHints::Never,
        closure_return_type_hints: ClosureReturnTypeHints::Never,
        adjustment_hints: AdjustmentHints::Never,
        adjustment_hints_mode: AdjustmentHintsMode::Prefix,
        adjustment_hints_hide_outside_unsafe: false,
        binding_mode_hints: false,
        hide_named_constructor_hints: false,
        hide_closure_initialization_hints: false,
        param_names_for_lifetime_elision_hints: false,
        max_length: None,
        closing_brace_hints_min_lines: None,
    };
    pub(super) const DISABLED_CONFIG_WITH_LINKS: InlayHintsConfig =
        InlayHintsConfig { location_links: true, ..DISABLED_CONFIG };
    pub(super) const TEST_CONFIG: InlayHintsConfig = InlayHintsConfig {
        type_hints: true,
        parameter_hints: true,
        chaining_hints: true,
        closure_return_type_hints: ClosureReturnTypeHints::WithBlock,
        binding_mode_hints: true,
        lifetime_elision_hints: LifetimeElisionHints::Always,
        ..DISABLED_CONFIG_WITH_LINKS
    };

    #[track_caller]
    pub(super) fn check(ra_fixture: &str) {
        check_with_config(TEST_CONFIG, ra_fixture);
    }

    #[track_caller]
    pub(super) fn check_with_config(config: InlayHintsConfig, ra_fixture: &str) {
        let (analysis, file_id) = fixture::file(ra_fixture);
        let mut expected = extract_annotations(&analysis.file_text(file_id).unwrap());
        let inlay_hints = analysis.inlay_hints(&config, file_id, None).unwrap();
        let actual = inlay_hints
            .into_iter()
            .map(|it| (it.range, it.label.to_string()))
            .sorted_by_key(|(range, _)| range.start())
            .collect::<Vec<_>>();
        expected.sort_by_key(|(range, _)| range.start());

        assert_eq!(expected, actual, "\nExpected:\n{expected:#?}\n\nActual:\n{actual:#?}");
    }

    #[track_caller]
    pub(super) fn check_expect(config: InlayHintsConfig, ra_fixture: &str, expect: Expect) {
        let (analysis, file_id) = fixture::file(ra_fixture);
        let inlay_hints = analysis.inlay_hints(&config, file_id, None).unwrap();
        expect.assert_debug_eq(&inlay_hints)
    }

    #[test]
    fn hints_disabled() {
        check_with_config(
            InlayHintsConfig { render_colons: true, ..DISABLED_CONFIG },
            r#"
fn foo(a: i32, b: i32) -> i32 { a + b }
fn main() {
    let _x = foo(4, 4);
}"#,
        );
    }
}
