// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

//! Recursive visitors for ast Nodes. See [`Visitor`] for more details.

use crate::ast::{AccessExpr, Action, AddDropSync, AfterMatchSkip, AlterColumnOperation, AlterConnectorOwner, AlterIndexOperation, AlterPolicyOperation, AlterRoleOperation, AlterTableAlgorithm, AlterTableLock, AlterTableOperation, AlterType, AlterTypeAddValue, AlterTypeAddValuePosition, AlterTypeOperation, AlterTypeRename, AlterTypeRenameValue, AnalyzeFormat, ArgMode, Array, ArrayElemTypeDef, Assignment, AssignmentTarget, AttachDuckDBDatabaseOption, AttachedToken, BeginTransactionKind, BinaryLength, BinaryOperator, CascadeOption, CaseStatement, CaseWhen, CastFormat, CastKind, CeilFloorKind, CharLengthUnits, CharacterLength, CloseCursor, ClusteredBy, ClusteredIndex, ColumnDef, ColumnOption, ColumnOptionDef, ColumnPolicy, ColumnPolicyProperty, CommentDef, CommentObject, ConditionalStatementBlock, ConditionalStatements, ConflictTarget, ConnectBy, ConstraintCharacteristics, ContextModifier, CopyIntoSnowflakeKind, CopyLegacyCsvOption, CopyLegacyOption, CopyOption, CopySource, CopyTarget, CreateConnector, CreateFunction, CreateFunctionBody, CreateFunctionUsing, CreateIndex, CreatePolicyCommand, CreatePolicyType, CreateTable, CreateTableOptions, CreateViewAlgorithm, CreateViewParams, CreateViewSecurity, Cte, CteAsMaterialized, DataType, DateTimeField, Declare, DeclareAssignment, DeclareType, Deduplicate, DeferrableInitial, Delete, DescribeAlias, DictionaryField, DiscardObject, Distinct, DoUpdate, DollarQuotedString, DropBehavior, DuplicateTreatment, EmptyMatchesMode, EnumMember, ExactNumberInfo, ExceptSelectItem, ExcludeSelectItem, Expr, ExprWithAlias, ExtractSyntax, Fetch, FetchDirection, FileFormat, FileStagingCommand, FlushLocation, FlushType, ForClause, ForXml, FormatClause, FromTable, Function, FunctionArg, FunctionArgExpr, FunctionArgumentClause, FunctionArgumentList, FunctionArguments, FunctionBehavior, FunctionCalledOnNull, FunctionDesc, FunctionDeterminismSpecifier, FunctionParallel, GeneratedAs, GeneratedExpressionMode, GeometricTypeKind, GrantObjects, Grantee, GranteeName, GranteesType, GroupByExpr, GroupByWithModifier, HavingBound, HavingBoundKind, HiveDelimiter, HiveDescribeFormat, HiveDistributionStyle, HiveFormat, HiveLoadDataFormat, HiveRowDelimiter, HiveRowFormat, HiveSetLocation, Ident, IdentWithAlias, IdentityParameters, IdentityProperty, IdentityPropertyFormatKind, IdentityPropertyKind, IdentityPropertyOrder, IfStatement, IlikeSelectItem, IndexColumn, IndexOption, IndexType, InputFormatClause, Insert, InsertAliases, Interpolate, InterpolateExpr, Interval, Join, JoinConstraint, JoinOperator, JsonNullClause, JsonPath, JsonPathElem, KeyOrIndexDisplay, KeyValueOptions, KillType, LambdaFunction, LateralView, LimitClause, ListAggOnOverflow, LockClause, LockTable, LockTableType, LockType, MacroArg, MacroDefinition, Map, MapEntry, MatchRecognizePattern, MatchRecognizeSymbol, Measure, MergeAction, MergeClause, MergeClauseKind, MergeInsertExpr, MergeInsertKind, Method, MinMaxValue, MySQLColumnPosition, MysqlInsertPriority, NamedWindowDefinition, NamedWindowExpr, NonBlock, NullTreatment, NullsDistinctOption, ObjectName, ObjectNamePart, ObjectType, Offset, OffsetRows, OnCommit, OnConflict, OnConflictAction, OneOrManyWithParens, OperateFunctionArg, OrderBy, OrderByExpr, OrderByKind, OrderByOptions, OutputClause, Owner, Partition, PartitionRangeDirection, Password, PivotValueSource, Privileges, ProcedureParam, ProjectionSelect, Query, RaisErrorOption, RaiseStatement, RaiseStatementValue, ReferentialAction, RenameSelectItem, RenameTable, RepetitionQuantifier, ReplaceSelectElement, ReplaceSelectItem, ResetConfig, RoleOption, RowAccessPolicy, RowsPerMatch, SchemaName, SearchModifier, SecondaryRoles, SecretOption, Select, SelectFlavor, SelectInto, SelectItem, SelectItemQualifiedWildcardKind, SequenceOptions, SessionParamStatsTopic, SessionParamValue, Set, SetAssignment, SetConfigValue, SetExpr, SetOperator, SetQuantifier, SetSessionParamGeneric, SetSessionParamIdentityInsert, SetSessionParamKind, SetSessionParamOffsets, SetSessionParamStatistics, Setting, ShowCreateObject, ShowObjects, ShowStatementFilter, ShowStatementFilterPosition, ShowStatementIn, ShowStatementInClause, ShowStatementInParentType, ShowStatementOptions, Span, SqlOption, SqliteOnConflict, StageLoadSelectItem, StageParamsObject, Statement, StorageSerializationPolicy, StructBracketKind, StructField, Subscript, SymbolDefinition, Table, TableAlias, TableAliasColumnDef, TableConstraint, TableEngine, TableFactor, TableFunctionArgs, TableIndexHintForClause, TableIndexHintType, TableIndexHints, TableIndexType, TableObject, TableOptionsClustered, TableSample, TableSampleBucket, TableSampleMethod, TableSampleModifier, TableSampleQuantity, TableSampleSeed, TableSampleSeedModifier, TableSampleUnit, TableVersion, TableWithJoins, Tag, TagsColumnOption, TimezoneInfo, Token, Top, TopQuantity, TransactionAccessMode, TransactionIsolationLevel, TransactionMode, TransactionModifier, TriggerEvent, TriggerExecBody, TriggerExecBodyType, TriggerObject, TriggerPeriod, TriggerReferencing, TriggerReferencingType, TrimWhereField, TruncateIdentityOption, UnaryOperator, UnionField, UpdateTableFromKind, Use, UserDefinedTypeCompositeAttributeDef, UserDefinedTypeRepresentation, UtilityOption, Value, ValueTableMode, ValueWithSpan, Values, ViewColumnDef, WildcardAdditionalOptions, WindowFrame, WindowFrameBound, WindowFrameUnits, WindowSpec, WindowType, With, WithFill, WrappedCollection};

use crate::ast::helpers::stmt_create_table::CreateTableBuilder;
use crate::ast::helpers::key_value_options::{KeyValueOption, KeyValueOptionType};
use crate::tokenizer::{Location, TokenWithSpan, Word, Whitespace};
use core::ops::ControlFlow;

/// A type that can be visited by a [`Visitor`]. See [`Visitor`] for
/// recursively visiting parsed SQL statements.
///
/// # Note
///
/// This trait should be automatically derived for sqlparser AST nodes
/// using the [Visit](sqlparser_derive::Visit) proc macro.
///
/// ```text
/// #[cfg_attr(feature = "visitor", derive(Visit, VisitMut))]
/// ```
pub trait Visit {
    fn visit<V: Visitor>(&self, visitor: &mut V) -> ControlFlow<V::Break>;
}

/// A type that can be visited by a [`VisitorMut`]. See [`VisitorMut`] for
/// recursively visiting parsed SQL statements.
///
/// # Note
///
/// This trait should be automatically derived for sqlparser AST nodes
/// using the [VisitMut](sqlparser_derive::VisitMut) proc macro.
///
/// ```text
/// #[cfg_attr(feature = "visitor", derive(Visit, VisitMut))]
/// ```
pub trait VisitMut {
    fn visit<V: VisitorMut>(&mut self, visitor: &mut V) -> ControlFlow<V::Break>;
}

impl<T: Visit> Visit for Option<T> {
    fn visit<V: Visitor>(&self, visitor: &mut V) -> ControlFlow<V::Break> {
        if let Some(s) = self {
            s.visit(visitor)?;
        }
        ControlFlow::Continue(())
    }
}

impl<T: Visit> Visit for Vec<T> {
    fn visit<V: Visitor>(&self, visitor: &mut V) -> ControlFlow<V::Break> {
        for v in self {
            v.visit(visitor)?;
        }
        ControlFlow::Continue(())
    }
}

impl<T: Visit> Visit for Box<T> {
    fn visit<V: Visitor>(&self, visitor: &mut V) -> ControlFlow<V::Break> {
        T::visit(self, visitor)
    }
}

impl<T: VisitMut> VisitMut for Option<T> {
    fn visit<V: VisitorMut>(&mut self, visitor: &mut V) -> ControlFlow<V::Break> {
        if let Some(s) = self {
            s.visit(visitor)?;
        }
        ControlFlow::Continue(())
    }
}

impl<T: VisitMut> VisitMut for Vec<T> {
    fn visit<V: VisitorMut>(&mut self, visitor: &mut V) -> ControlFlow<V::Break> {
        for v in self {
            v.visit(visitor)?;
        }
        ControlFlow::Continue(())
    }
}

impl<T: VisitMut> VisitMut for Box<T> {
    fn visit<V: VisitorMut>(&mut self, visitor: &mut V) -> ControlFlow<V::Break> {
        T::visit(self, visitor)
    }
}

macro_rules! visit_noop {
    ($($t:ty),+) => {
        $(impl Visit for $t {
            fn visit<V: Visitor>(&self, _visitor: &mut V) -> ControlFlow<V::Break> {
               ControlFlow::Continue(())
            }
        })+
        $(impl VisitMut for $t {
            fn visit<V: VisitorMut>(&mut self, _visitor: &mut V) -> ControlFlow<V::Break> {
               ControlFlow::Continue(())
            }
        })+
    };
}

visit_noop!(u8, u16, u32, u64, i8, i16, i32, i64, char, bool, String);

#[cfg(feature = "bigdecimal")]
visit_noop!(bigdecimal::BigDecimal);

/// A visitor that can be used to walk an AST tree.
///
/// `pre_visit_` methods are invoked before visiting all children of the
/// node and `post_visit_` methods are invoked after visiting all
/// children of the node.
///
/// # See also
///
/// These methods provide a more concise way of visiting nodes of a certain type:
/// * [visit_relations]
/// * [visit_expressions]
/// * [visit_statements]
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{Visit, Visitor, ObjectName, Expr};
/// # use core::ops::ControlFlow;
/// // A structure that records statements and relations
/// #[derive(Default)]
/// struct V {
///    visited: Vec<String>,
/// }
///
/// // Visit relations and exprs before children are visited (depth first walk)
/// // Note you can also visit statements and visit exprs after children have been visited
/// impl Visitor for V {
///   type Break = ();
///
///   fn pre_visit_relation(&mut self, relation: &ObjectName) -> ControlFlow<Self::Break> {
///     self.visited.push(format!("PRE: RELATION: {}", relation));
///     ControlFlow::Continue(())
///   }
///
///   fn pre_visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::Break> {
///     self.visited.push(format!("PRE: EXPR: {}", expr));
///     ControlFlow::Continue(())
///   }
/// }
///
/// let sql = "SELECT a FROM foo where x IN (SELECT y FROM bar)";
/// let statements = Parser::parse_sql(&GenericDialect{}, sql)
///    .unwrap();
///
/// // Drive the visitor through the AST
/// let mut visitor = V::default();
/// statements.visit(&mut visitor);
///
/// // The visitor has visited statements and expressions in pre-traversal order
/// let expected : Vec<_> = [
///   "PRE: EXPR: a",
///   "PRE: RELATION: foo",
///   "PRE: EXPR: x IN (SELECT y FROM bar)",
///   "PRE: EXPR: x",
///   "PRE: EXPR: y",
///   "PRE: RELATION: bar",
/// ]
///   .into_iter().map(|s| s.to_string()).collect();
///
/// assert_eq!(visitor.visited, expected);
/// ```
pub trait Visitor {
    /// Type returned when the recursion returns early.
    type Break;

    /// Invoked for any queries that appear in the AST before visiting children
    fn pre_visit_query(&mut self, _query: &Query) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any queries that appear in the AST after visiting children
    fn post_visit_query(&mut self, _query: &Query) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any relations (e.g. tables) that appear in the AST before visiting children
    fn pre_visit_relation(&mut self, _relation: &ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any relations (e.g. tables) that appear in the AST after visiting children
    fn post_visit_relation(&mut self, _relation: &ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table factors that appear in the AST before visiting children
    fn pre_visit_table_factor(&mut self, _table_factor: &TableFactor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table factors that appear in the AST after visiting children
    fn post_visit_table_factor(&mut self, _table_factor: &TableFactor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expressions that appear in the AST before visiting children
    fn pre_visit_expr(&mut self, _expr: &Expr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expressions that appear in the AST
    fn post_visit_expr(&mut self, _expr: &Expr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any statements that appear in the AST before visiting children
    fn pre_visit_statement(&mut self, _statement: &Statement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any statements that appear in the AST after visiting children
    fn post_visit_statement(&mut self, _statement: &Statement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any Value that appear in the AST before visiting children
    fn pre_visit_value(&mut self, _value: &Value) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any Value that appear in the AST after visiting children
    fn post_visit_value(&mut self, _value: &Value) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any access expr that appear in the AST before visiting children
    fn pre_visit_access_expr(&mut self, _access_expr: &AccessExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any access expr that appear in the AST after visiting children
    fn post_visit_access_expr(&mut self, _access_expr: &AccessExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any action that appear in the AST before visiting children
    fn pre_visit_action(&mut self, _action: &Action) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any action that appear in the AST after visiting children
    fn post_visit_action(&mut self, _action: &Action) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any add drop sync that appear in the AST before visiting children
    fn pre_visit_add_drop_sync(&mut self, _add_drop_sync: &AddDropSync) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any add drop sync that appear in the AST after visiting children
    fn post_visit_add_drop_sync(&mut self, _add_drop_sync: &AddDropSync) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any after match skip that appear in the AST before visiting children
    fn pre_visit_after_match_skip(&mut self, _after_match_skip: &AfterMatchSkip) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any after match skip that appear in the AST after visiting children
    fn post_visit_after_match_skip(&mut self, _after_match_skip: &AfterMatchSkip) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter column operation that appear in the AST before visiting children
    fn pre_visit_alter_column_operation(&mut self, _alter_column_operation: &AlterColumnOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter column operation that appear in the AST after visiting children
    fn post_visit_alter_column_operation(&mut self, _alter_column_operation: &AlterColumnOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter connector owner that appear in the AST before visiting children
    fn pre_visit_alter_connector_owner(&mut self, _alter_connector_owner: &AlterConnectorOwner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter connector owner that appear in the AST after visiting children
    fn post_visit_alter_connector_owner(&mut self, _alter_connector_owner: &AlterConnectorOwner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter index operation that appear in the AST before visiting children
    fn pre_visit_alter_index_operation(&mut self, _alter_index_operation: &AlterIndexOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter index operation that appear in the AST after visiting children
    fn post_visit_alter_index_operation(&mut self, _alter_index_operation: &AlterIndexOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter policy operation that appear in the AST before visiting children
    fn pre_visit_alter_policy_operation(&mut self, _alter_policy_operation: &AlterPolicyOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter policy operation that appear in the AST after visiting children
    fn post_visit_alter_policy_operation(&mut self, _alter_policy_operation: &AlterPolicyOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter role operation that appear in the AST before visiting children
    fn pre_visit_alter_role_operation(&mut self, _alter_role_operation: &AlterRoleOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter role operation that appear in the AST after visiting children
    fn post_visit_alter_role_operation(&mut self, _alter_role_operation: &AlterRoleOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table algorithm that appear in the AST before visiting children
    fn pre_visit_alter_table_algorithm(&mut self, _alter_table_algorithm: &AlterTableAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table algorithm that appear in the AST after visiting children
    fn post_visit_alter_table_algorithm(&mut self, _alter_table_algorithm: &AlterTableAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table lock that appear in the AST before visiting children
    fn pre_visit_alter_table_lock(&mut self, _alter_table_lock: &AlterTableLock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table lock that appear in the AST after visiting children
    fn post_visit_alter_table_lock(&mut self, _alter_table_lock: &AlterTableLock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table operation that appear in the AST before visiting children
    fn pre_visit_alter_table_operation(&mut self, _alter_table_operation: &AlterTableOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table operation that appear in the AST after visiting children
    fn post_visit_alter_table_operation(&mut self, _alter_table_operation: &AlterTableOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type that appear in the AST before visiting children
    fn pre_visit_alter_type(&mut self, _alter_type: &AlterType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type that appear in the AST after visiting children
    fn post_visit_alter_type(&mut self, _alter_type: &AlterType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value that appear in the AST before visiting children
    fn pre_visit_alter_type_add_value(&mut self, _alter_type_add_value: &AlterTypeAddValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value that appear in the AST after visiting children
    fn post_visit_alter_type_add_value(&mut self, _alter_type_add_value: &AlterTypeAddValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value position that appear in the AST before visiting children
    fn pre_visit_alter_type_add_value_position(&mut self, _alter_type_add_value_position: &AlterTypeAddValuePosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value position that appear in the AST after visiting children
    fn post_visit_alter_type_add_value_position(&mut self, _alter_type_add_value_position: &AlterTypeAddValuePosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type operation that appear in the AST before visiting children
    fn pre_visit_alter_type_operation(&mut self, _alter_type_operation: &AlterTypeOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type operation that appear in the AST after visiting children
    fn post_visit_alter_type_operation(&mut self, _alter_type_operation: &AlterTypeOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename that appear in the AST before visiting children
    fn pre_visit_alter_type_rename(&mut self, _alter_type_rename: &AlterTypeRename) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename that appear in the AST after visiting children
    fn post_visit_alter_type_rename(&mut self, _alter_type_rename: &AlterTypeRename) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename value that appear in the AST before visiting children
    fn pre_visit_alter_type_rename_value(&mut self, _alter_type_rename_value: &AlterTypeRenameValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename value that appear in the AST after visiting children
    fn post_visit_alter_type_rename_value(&mut self, _alter_type_rename_value: &AlterTypeRenameValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any analyze format that appear in the AST before visiting children
    fn pre_visit_analyze_format(&mut self, _analyze_format: &AnalyzeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any analyze format that appear in the AST after visiting children
    fn post_visit_analyze_format(&mut self, _analyze_format: &AnalyzeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any arg mode that appear in the AST before visiting children
    fn pre_visit_arg_mode(&mut self, _arg_mode: &ArgMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any arg mode that appear in the AST after visiting children
    fn post_visit_arg_mode(&mut self, _arg_mode: &ArgMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array that appear in the AST before visiting children
    fn pre_visit_array(&mut self, _array: &Array) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array that appear in the AST after visiting children
    fn post_visit_array(&mut self, _array: &Array) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array elem type def that appear in the AST before visiting children
    fn pre_visit_array_elem_type_def(&mut self, _array_elem_type_def: &ArrayElemTypeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array elem type def that appear in the AST after visiting children
    fn post_visit_array_elem_type_def(&mut self, _array_elem_type_def: &ArrayElemTypeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment that appear in the AST before visiting children
    fn pre_visit_assignment(&mut self, _assignment: &Assignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment that appear in the AST after visiting children
    fn post_visit_assignment(&mut self, _assignment: &Assignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment target that appear in the AST before visiting children
    fn pre_visit_assignment_target(&mut self, _assignment_target: &AssignmentTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment target that appear in the AST after visiting children
    fn post_visit_assignment_target(&mut self, _assignment_target: &AssignmentTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attach duck db database option that appear in the AST before visiting children
    fn pre_visit_attach_duck_db_database_option(&mut self, _attach_duck_db_database_option: &AttachDuckDBDatabaseOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attach duck db database option that appear in the AST after visiting children
    fn post_visit_attach_duck_db_database_option(&mut self, _attach_duck_db_database_option: &AttachDuckDBDatabaseOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attached token that appear in the AST before visiting children
    fn pre_visit_attached_token(&mut self, _attached_token: &AttachedToken) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attached token that appear in the AST after visiting children
    fn post_visit_attached_token(&mut self, _attached_token: &AttachedToken) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any begin transaction kind that appear in the AST before visiting children
    fn pre_visit_begin_transaction_kind(&mut self, _begin_transaction_kind: &BeginTransactionKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any begin transaction kind that appear in the AST after visiting children
    fn post_visit_begin_transaction_kind(&mut self, _begin_transaction_kind: &BeginTransactionKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary length that appear in the AST before visiting children
    fn pre_visit_binary_length(&mut self, _binary_length: &BinaryLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary length that appear in the AST after visiting children
    fn post_visit_binary_length(&mut self, _binary_length: &BinaryLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary operator that appear in the AST before visiting children
    fn pre_visit_binary_operator(&mut self, _binary_operator: &BinaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary operator that appear in the AST after visiting children
    fn post_visit_binary_operator(&mut self, _binary_operator: &BinaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cascade option that appear in the AST before visiting children
    fn pre_visit_cascade_option(&mut self, _cascade_option: &CascadeOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cascade option that appear in the AST after visiting children
    fn post_visit_cascade_option(&mut self, _cascade_option: &CascadeOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case statement that appear in the AST before visiting children
    fn pre_visit_case_statement(&mut self, _case_statement: &CaseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case statement that appear in the AST after visiting children
    fn post_visit_case_statement(&mut self, _case_statement: &CaseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case when that appear in the AST before visiting children
    fn pre_visit_case_when(&mut self, _case_when: &CaseWhen) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case when that appear in the AST after visiting children
    fn post_visit_case_when(&mut self, _case_when: &CaseWhen) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast format that appear in the AST before visiting children
    fn pre_visit_cast_format(&mut self, _cast_format: &CastFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast format that appear in the AST after visiting children
    fn post_visit_cast_format(&mut self, _cast_format: &CastFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast kind that appear in the AST before visiting children
    fn pre_visit_cast_kind(&mut self, _cast_kind: &CastKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast kind that appear in the AST after visiting children
    fn post_visit_cast_kind(&mut self, _cast_kind: &CastKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ceil floor kind that appear in the AST before visiting children
    fn pre_visit_ceil_floor_kind(&mut self, _ceil_floor_kind: &CeilFloorKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ceil floor kind that appear in the AST after visiting children
    fn post_visit_ceil_floor_kind(&mut self, _ceil_floor_kind: &CeilFloorKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any char length units that appear in the AST before visiting children
    fn pre_visit_char_length_units(&mut self, _char_length_units: &CharLengthUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any char length units that appear in the AST after visiting children
    fn post_visit_char_length_units(&mut self, _char_length_units: &CharLengthUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any character length that appear in the AST before visiting children
    fn pre_visit_character_length(&mut self, _character_length: &CharacterLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any character length that appear in the AST after visiting children
    fn post_visit_character_length(&mut self, _character_length: &CharacterLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any close cursor that appear in the AST before visiting children
    fn pre_visit_close_cursor(&mut self, _close_cursor: &CloseCursor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any close cursor that appear in the AST after visiting children
    fn post_visit_close_cursor(&mut self, _close_cursor: &CloseCursor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered by that appear in the AST before visiting children
    fn pre_visit_clustered_by(&mut self, _clustered_by: &ClusteredBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered by that appear in the AST after visiting children
    fn post_visit_clustered_by(&mut self, _clustered_by: &ClusteredBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered index that appear in the AST before visiting children
    fn pre_visit_clustered_index(&mut self, _clustered_index: &ClusteredIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered index that appear in the AST after visiting children
    fn post_visit_clustered_index(&mut self, _clustered_index: &ClusteredIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column def that appear in the AST before visiting children
    fn pre_visit_column_def(&mut self, _column_def: &ColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column def that appear in the AST after visiting children
    fn post_visit_column_def(&mut self, _column_def: &ColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option that appear in the AST before visiting children
    fn pre_visit_column_option(&mut self, _column_option: &ColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option that appear in the AST after visiting children
    fn post_visit_column_option(&mut self, _column_option: &ColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option def that appear in the AST before visiting children
    fn pre_visit_column_option_def(&mut self, _column_option_def: &ColumnOptionDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option def that appear in the AST after visiting children
    fn post_visit_column_option_def(&mut self, _column_option_def: &ColumnOptionDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy that appear in the AST before visiting children
    fn pre_visit_column_policy(&mut self, _column_policy: &ColumnPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy that appear in the AST after visiting children
    fn post_visit_column_policy(&mut self, _column_policy: &ColumnPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy property that appear in the AST before visiting children
    fn pre_visit_column_policy_property(&mut self, _column_policy_property: &ColumnPolicyProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy property that appear in the AST after visiting children
    fn post_visit_column_policy_property(&mut self, _column_policy_property: &ColumnPolicyProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment def that appear in the AST before visiting children
    fn pre_visit_comment_def(&mut self, _comment_def: &CommentDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment def that appear in the AST after visiting children
    fn post_visit_comment_def(&mut self, _comment_def: &CommentDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment object that appear in the AST before visiting children
    fn pre_visit_comment_object(&mut self, _comment_object: &CommentObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment object that appear in the AST after visiting children
    fn post_visit_comment_object(&mut self, _comment_object: &CommentObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statement block that appear in the AST before visiting children
    fn pre_visit_conditional_statement_block(&mut self, _conditional_statement_block: &ConditionalStatementBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statement block that appear in the AST after visiting children
    fn post_visit_conditional_statement_block(&mut self, _conditional_statement_block: &ConditionalStatementBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statements that appear in the AST before visiting children
    fn pre_visit_conditional_statements(&mut self, _conditional_statements: &ConditionalStatements) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statements that appear in the AST after visiting children
    fn post_visit_conditional_statements(&mut self, _conditional_statements: &ConditionalStatements) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conflict target that appear in the AST before visiting children
    fn pre_visit_conflict_target(&mut self, _conflict_target: &ConflictTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conflict target that appear in the AST after visiting children
    fn post_visit_conflict_target(&mut self, _conflict_target: &ConflictTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any connect by that appear in the AST before visiting children
    fn pre_visit_connect_by(&mut self, _connect_by: &ConnectBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any connect by that appear in the AST after visiting children
    fn post_visit_connect_by(&mut self, _connect_by: &ConnectBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any constraint characteristics that appear in the AST before visiting children
    fn pre_visit_constraint_characteristics(&mut self, _constraint_characteristics: &ConstraintCharacteristics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any constraint characteristics that appear in the AST after visiting children
    fn post_visit_constraint_characteristics(&mut self, _constraint_characteristics: &ConstraintCharacteristics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any context modifier that appear in the AST before visiting children
    fn pre_visit_context_modifier(&mut self, _context_modifier: &ContextModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any context modifier that appear in the AST after visiting children
    fn post_visit_context_modifier(&mut self, _context_modifier: &ContextModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy into snowflake kind that appear in the AST before visiting children
    fn pre_visit_copy_into_snowflake_kind(&mut self, _copy_into_snowflake_kind: &CopyIntoSnowflakeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy into snowflake kind that appear in the AST after visiting children
    fn post_visit_copy_into_snowflake_kind(&mut self, _copy_into_snowflake_kind: &CopyIntoSnowflakeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy csv option that appear in the AST before visiting children
    fn pre_visit_copy_legacy_csv_option(&mut self, _copy_legacy_csv_option: &CopyLegacyCsvOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy csv option that appear in the AST after visiting children
    fn post_visit_copy_legacy_csv_option(&mut self, _copy_legacy_csv_option: &CopyLegacyCsvOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy option that appear in the AST before visiting children
    fn pre_visit_copy_legacy_option(&mut self, _copy_legacy_option: &CopyLegacyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy option that appear in the AST after visiting children
    fn post_visit_copy_legacy_option(&mut self, _copy_legacy_option: &CopyLegacyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy option that appear in the AST before visiting children
    fn pre_visit_copy_option(&mut self, _copy_option: &CopyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy option that appear in the AST after visiting children
    fn post_visit_copy_option(&mut self, _copy_option: &CopyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy source that appear in the AST before visiting children
    fn pre_visit_copy_source(&mut self, _copy_source: &CopySource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy source that appear in the AST after visiting children
    fn post_visit_copy_source(&mut self, _copy_source: &CopySource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy target that appear in the AST before visiting children
    fn pre_visit_copy_target(&mut self, _copy_target: &CopyTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy target that appear in the AST after visiting children
    fn post_visit_copy_target(&mut self, _copy_target: &CopyTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create connector that appear in the AST before visiting children
    fn pre_visit_create_connector(&mut self, _create_connector: &CreateConnector) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create connector that appear in the AST after visiting children
    fn post_visit_create_connector(&mut self, _create_connector: &CreateConnector) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function that appear in the AST before visiting children
    fn pre_visit_create_function(&mut self, _create_function: &CreateFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function that appear in the AST after visiting children
    fn post_visit_create_function(&mut self, _create_function: &CreateFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function body that appear in the AST before visiting children
    fn pre_visit_create_function_body(&mut self, _create_function_body: &CreateFunctionBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function body that appear in the AST after visiting children
    fn post_visit_create_function_body(&mut self, _create_function_body: &CreateFunctionBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function using that appear in the AST before visiting children
    fn pre_visit_create_function_using(&mut self, _create_function_using: &CreateFunctionUsing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function using that appear in the AST after visiting children
    fn post_visit_create_function_using(&mut self, _create_function_using: &CreateFunctionUsing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create index that appear in the AST before visiting children
    fn pre_visit_create_index(&mut self, _create_index: &CreateIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create index that appear in the AST after visiting children
    fn post_visit_create_index(&mut self, _create_index: &CreateIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy command that appear in the AST before visiting children
    fn pre_visit_create_policy_command(&mut self, _create_policy_command: &CreatePolicyCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy command that appear in the AST after visiting children
    fn post_visit_create_policy_command(&mut self, _create_policy_command: &CreatePolicyCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy type that appear in the AST before visiting children
    fn pre_visit_create_policy_type(&mut self, _create_policy_type: &CreatePolicyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy type that appear in the AST after visiting children
    fn post_visit_create_policy_type(&mut self, _create_policy_type: &CreatePolicyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table that appear in the AST before visiting children
    fn pre_visit_create_table(&mut self, _create_table: &CreateTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table that appear in the AST after visiting children
    fn post_visit_create_table(&mut self, _create_table: &CreateTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table builder that appear in the AST before visiting children
    fn pre_visit_create_table_builder(&mut self, _create_table_builder: &CreateTableBuilder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table builder that appear in the AST after visiting children
    fn post_visit_create_table_builder(&mut self, _create_table_builder: &CreateTableBuilder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table options that appear in the AST before visiting children
    fn pre_visit_create_table_options(&mut self, _create_table_options: &CreateTableOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table options that appear in the AST after visiting children
    fn post_visit_create_table_options(&mut self, _create_table_options: &CreateTableOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view algorithm that appear in the AST before visiting children
    fn pre_visit_create_view_algorithm(&mut self, _create_view_algorithm: &CreateViewAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view algorithm that appear in the AST after visiting children
    fn post_visit_create_view_algorithm(&mut self, _create_view_algorithm: &CreateViewAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view params that appear in the AST before visiting children
    fn pre_visit_create_view_params(&mut self, _create_view_params: &CreateViewParams) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view params that appear in the AST after visiting children
    fn post_visit_create_view_params(&mut self, _create_view_params: &CreateViewParams) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view security that appear in the AST before visiting children
    fn pre_visit_create_view_security(&mut self, _create_view_security: &CreateViewSecurity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view security that appear in the AST after visiting children
    fn post_visit_create_view_security(&mut self, _create_view_security: &CreateViewSecurity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte that appear in the AST before visiting children
    fn pre_visit_cte(&mut self, _cte: &Cte) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte that appear in the AST after visiting children
    fn post_visit_cte(&mut self, _cte: &Cte) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte as materialized that appear in the AST before visiting children
    fn pre_visit_cte_as_materialized(&mut self, _cte_as_materialized: &CteAsMaterialized) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte as materialized that appear in the AST after visiting children
    fn post_visit_cte_as_materialized(&mut self, _cte_as_materialized: &CteAsMaterialized) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any data type that appear in the AST before visiting children
    fn pre_visit_data_type(&mut self, _data_type: &DataType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any data type that appear in the AST after visiting children
    fn post_visit_data_type(&mut self, _data_type: &DataType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any date time field that appear in the AST before visiting children
    fn pre_visit_date_time_field(&mut self, _date_time_field: &DateTimeField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any date time field that appear in the AST after visiting children
    fn post_visit_date_time_field(&mut self, _date_time_field: &DateTimeField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare that appear in the AST before visiting children
    fn pre_visit_declare(&mut self, _declare: &Declare) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare that appear in the AST after visiting children
    fn post_visit_declare(&mut self, _declare: &Declare) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare assignment that appear in the AST before visiting children
    fn pre_visit_declare_assignment(&mut self, _declare_assignment: &DeclareAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare assignment that appear in the AST after visiting children
    fn post_visit_declare_assignment(&mut self, _declare_assignment: &DeclareAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare type that appear in the AST before visiting children
    fn pre_visit_declare_type(&mut self, _declare_type: &DeclareType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare type that appear in the AST after visiting children
    fn post_visit_declare_type(&mut self, _declare_type: &DeclareType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deduplicate that appear in the AST before visiting children
    fn pre_visit_deduplicate(&mut self, _deduplicate: &Deduplicate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deduplicate that appear in the AST after visiting children
    fn post_visit_deduplicate(&mut self, _deduplicate: &Deduplicate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deferrable initial that appear in the AST before visiting children
    fn pre_visit_deferrable_initial(&mut self, _deferrable_initial: &DeferrableInitial) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deferrable initial that appear in the AST after visiting children
    fn post_visit_deferrable_initial(&mut self, _deferrable_initial: &DeferrableInitial) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any delete that appear in the AST before visiting children
    fn pre_visit_delete(&mut self, _delete: &Delete) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any delete that appear in the AST after visiting children
    fn post_visit_delete(&mut self, _delete: &Delete) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any describe alias that appear in the AST before visiting children
    fn pre_visit_describe_alias(&mut self, _describe_alias: &DescribeAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any describe alias that appear in the AST after visiting children
    fn post_visit_describe_alias(&mut self, _describe_alias: &DescribeAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dictionary field that appear in the AST before visiting children
    fn pre_visit_dictionary_field(&mut self, _dictionary_field: &DictionaryField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dictionary field that appear in the AST after visiting children
    fn post_visit_dictionary_field(&mut self, _dictionary_field: &DictionaryField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any discard object that appear in the AST before visiting children
    fn pre_visit_discard_object(&mut self, _discard_object: &DiscardObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any discard object that appear in the AST after visiting children
    fn post_visit_discard_object(&mut self, _discard_object: &DiscardObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any distinct that appear in the AST before visiting children
    fn pre_visit_distinct(&mut self, _distinct: &Distinct) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any distinct that appear in the AST after visiting children
    fn post_visit_distinct(&mut self, _distinct: &Distinct) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any do update that appear in the AST before visiting children
    fn pre_visit_do_update(&mut self, _do_update: &DoUpdate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any do update that appear in the AST after visiting children
    fn post_visit_do_update(&mut self, _do_update: &DoUpdate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dollar quoted string that appear in the AST before visiting children
    fn pre_visit_dollar_quoted_string(&mut self, _dollar_quoted_string: &DollarQuotedString) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dollar quoted string that appear in the AST after visiting children
    fn post_visit_dollar_quoted_string(&mut self, _dollar_quoted_string: &DollarQuotedString) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any drop behavior that appear in the AST before visiting children
    fn pre_visit_drop_behavior(&mut self, _drop_behavior: &DropBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any drop behavior that appear in the AST after visiting children
    fn post_visit_drop_behavior(&mut self, _drop_behavior: &DropBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any duplicate treatment that appear in the AST before visiting children
    fn pre_visit_duplicate_treatment(&mut self, _duplicate_treatment: &DuplicateTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any duplicate treatment that appear in the AST after visiting children
    fn post_visit_duplicate_treatment(&mut self, _duplicate_treatment: &DuplicateTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any empty matches mode that appear in the AST before visiting children
    fn pre_visit_empty_matches_mode(&mut self, _empty_matches_mode: &EmptyMatchesMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any empty matches mode that appear in the AST after visiting children
    fn post_visit_empty_matches_mode(&mut self, _empty_matches_mode: &EmptyMatchesMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any enum member that appear in the AST before visiting children
    fn pre_visit_enum_member(&mut self, _enum_member: &EnumMember) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any enum member that appear in the AST after visiting children
    fn post_visit_enum_member(&mut self, _enum_member: &EnumMember) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exact number info that appear in the AST before visiting children
    fn pre_visit_exact_number_info(&mut self, _exact_number_info: &ExactNumberInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exact number info that appear in the AST after visiting children
    fn post_visit_exact_number_info(&mut self, _exact_number_info: &ExactNumberInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any except select item that appear in the AST before visiting children
    fn pre_visit_except_select_item(&mut self, _except_select_item: &ExceptSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any except select item that appear in the AST after visiting children
    fn post_visit_except_select_item(&mut self, _except_select_item: &ExceptSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exclude select item that appear in the AST before visiting children
    fn pre_visit_exclude_select_item(&mut self, _exclude_select_item: &ExcludeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exclude select item that appear in the AST after visiting children
    fn post_visit_exclude_select_item(&mut self, _exclude_select_item: &ExcludeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expr with alias that appear in the AST before visiting children
    fn pre_visit_expr_with_alias(&mut self, _expr_with_alias: &ExprWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expr with alias that appear in the AST after visiting children
    fn post_visit_expr_with_alias(&mut self, _expr_with_alias: &ExprWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any extract syntax that appear in the AST before visiting children
    fn pre_visit_extract_syntax(&mut self, _extract_syntax: &ExtractSyntax) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any extract syntax that appear in the AST after visiting children
    fn post_visit_extract_syntax(&mut self, _extract_syntax: &ExtractSyntax) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch that appear in the AST before visiting children
    fn pre_visit_fetch(&mut self, _fetch: &Fetch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch that appear in the AST after visiting children
    fn post_visit_fetch(&mut self, _fetch: &Fetch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch direction that appear in the AST before visiting children
    fn pre_visit_fetch_direction(&mut self, _fetch_direction: &FetchDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch direction that appear in the AST after visiting children
    fn post_visit_fetch_direction(&mut self, _fetch_direction: &FetchDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file format that appear in the AST before visiting children
    fn pre_visit_file_format(&mut self, _file_format: &FileFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file format that appear in the AST after visiting children
    fn post_visit_file_format(&mut self, _file_format: &FileFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file staging command that appear in the AST before visiting children
    fn pre_visit_file_staging_command(&mut self, _file_staging_command: &FileStagingCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file staging command that appear in the AST after visiting children
    fn post_visit_file_staging_command(&mut self, _file_staging_command: &FileStagingCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush location that appear in the AST before visiting children
    fn pre_visit_flush_location(&mut self, _flush_location: &FlushLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush location that appear in the AST after visiting children
    fn post_visit_flush_location(&mut self, _flush_location: &FlushLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush type that appear in the AST before visiting children
    fn pre_visit_flush_type(&mut self, _flush_type: &FlushType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush type that appear in the AST after visiting children
    fn post_visit_flush_type(&mut self, _flush_type: &FlushType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for clause that appear in the AST before visiting children
    fn pre_visit_for_clause(&mut self, _for_clause: &ForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for clause that appear in the AST after visiting children
    fn post_visit_for_clause(&mut self, _for_clause: &ForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for xml that appear in the AST before visiting children
    fn pre_visit_for_xml(&mut self, _for_xml: &ForXml) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for xml that appear in the AST after visiting children
    fn post_visit_for_xml(&mut self, _for_xml: &ForXml) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any format clause that appear in the AST before visiting children
    fn pre_visit_format_clause(&mut self, _format_clause: &FormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any format clause that appear in the AST after visiting children
    fn post_visit_format_clause(&mut self, _format_clause: &FormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any from table that appear in the AST before visiting children
    fn pre_visit_from_table(&mut self, _from_table: &FromTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any from table that appear in the AST after visiting children
    fn post_visit_from_table(&mut self, _from_table: &FromTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function that appear in the AST before visiting children
    fn pre_visit_function(&mut self, _function: &Function) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function that appear in the AST after visiting children
    fn post_visit_function(&mut self, _function: &Function) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg that appear in the AST before visiting children
    fn pre_visit_function_arg(&mut self, _function_arg: &FunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg that appear in the AST after visiting children
    fn post_visit_function_arg(&mut self, _function_arg: &FunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg expr that appear in the AST before visiting children
    fn pre_visit_function_arg_expr(&mut self, _function_arg_expr: &FunctionArgExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg expr that appear in the AST after visiting children
    fn post_visit_function_arg_expr(&mut self, _function_arg_expr: &FunctionArgExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument clause that appear in the AST before visiting children
    fn pre_visit_function_argument_clause(&mut self, _function_argument_clause: &FunctionArgumentClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument clause that appear in the AST after visiting children
    fn post_visit_function_argument_clause(&mut self, _function_argument_clause: &FunctionArgumentClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument list that appear in the AST before visiting children
    fn pre_visit_function_argument_list(&mut self, _function_argument_list: &FunctionArgumentList) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument list that appear in the AST after visiting children
    fn post_visit_function_argument_list(&mut self, _function_argument_list: &FunctionArgumentList) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arguments that appear in the AST before visiting children
    fn pre_visit_function_arguments(&mut self, _function_arguments: &FunctionArguments) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arguments that appear in the AST after visiting children
    fn post_visit_function_arguments(&mut self, _function_arguments: &FunctionArguments) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function behavior that appear in the AST before visiting children
    fn pre_visit_function_behavior(&mut self, _function_behavior: &FunctionBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function behavior that appear in the AST after visiting children
    fn post_visit_function_behavior(&mut self, _function_behavior: &FunctionBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function called on null that appear in the AST before visiting children
    fn pre_visit_function_called_on_null(&mut self, _function_called_on_null: &FunctionCalledOnNull) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function called on null that appear in the AST after visiting children
    fn post_visit_function_called_on_null(&mut self, _function_called_on_null: &FunctionCalledOnNull) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function desc that appear in the AST before visiting children
    fn pre_visit_function_desc(&mut self, _function_desc: &FunctionDesc) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function desc that appear in the AST after visiting children
    fn post_visit_function_desc(&mut self, _function_desc: &FunctionDesc) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function determinism specifier that appear in the AST before visiting children
    fn pre_visit_function_determinism_specifier(&mut self, _function_determinism_specifier: &FunctionDeterminismSpecifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function determinism specifier that appear in the AST after visiting children
    fn post_visit_function_determinism_specifier(&mut self, _function_determinism_specifier: &FunctionDeterminismSpecifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function parallel that appear in the AST before visiting children
    fn pre_visit_function_parallel(&mut self, _function_parallel: &FunctionParallel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function parallel that appear in the AST after visiting children
    fn post_visit_function_parallel(&mut self, _function_parallel: &FunctionParallel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated as that appear in the AST before visiting children
    fn pre_visit_generated_as(&mut self, _generated_as: &GeneratedAs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated as that appear in the AST after visiting children
    fn post_visit_generated_as(&mut self, _generated_as: &GeneratedAs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated expression mode that appear in the AST before visiting children
    fn pre_visit_generated_expression_mode(&mut self, _generated_expression_mode: &GeneratedExpressionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated expression mode that appear in the AST after visiting children
    fn post_visit_generated_expression_mode(&mut self, _generated_expression_mode: &GeneratedExpressionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any geometric type kind that appear in the AST before visiting children
    fn pre_visit_geometric_type_kind(&mut self, _geometric_type_kind: &GeometricTypeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any geometric type kind that appear in the AST after visiting children
    fn post_visit_geometric_type_kind(&mut self, _geometric_type_kind: &GeometricTypeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grant objects that appear in the AST before visiting children
    fn pre_visit_grant_objects(&mut self, _grant_objects: &GrantObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grant objects that appear in the AST after visiting children
    fn post_visit_grant_objects(&mut self, _grant_objects: &GrantObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee that appear in the AST before visiting children
    fn pre_visit_grantee(&mut self, _grantee: &Grantee) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee that appear in the AST after visiting children
    fn post_visit_grantee(&mut self, _grantee: &Grantee) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee name that appear in the AST before visiting children
    fn pre_visit_grantee_name(&mut self, _grantee_name: &GranteeName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee name that appear in the AST after visiting children
    fn post_visit_grantee_name(&mut self, _grantee_name: &GranteeName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantees type that appear in the AST before visiting children
    fn pre_visit_grantees_type(&mut self, _grantees_type: &GranteesType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantees type that appear in the AST after visiting children
    fn post_visit_grantees_type(&mut self, _grantees_type: &GranteesType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by expr that appear in the AST before visiting children
    fn pre_visit_group_by_expr(&mut self, _group_by_expr: &GroupByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by expr that appear in the AST after visiting children
    fn post_visit_group_by_expr(&mut self, _group_by_expr: &GroupByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by with modifier that appear in the AST before visiting children
    fn pre_visit_group_by_with_modifier(&mut self, _group_by_with_modifier: &GroupByWithModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by with modifier that appear in the AST after visiting children
    fn post_visit_group_by_with_modifier(&mut self, _group_by_with_modifier: &GroupByWithModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound that appear in the AST before visiting children
    fn pre_visit_having_bound(&mut self, _having_bound: &HavingBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound that appear in the AST after visiting children
    fn post_visit_having_bound(&mut self, _having_bound: &HavingBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound kind that appear in the AST before visiting children
    fn pre_visit_having_bound_kind(&mut self, _having_bound_kind: &HavingBoundKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound kind that appear in the AST after visiting children
    fn post_visit_having_bound_kind(&mut self, _having_bound_kind: &HavingBoundKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive delimiter that appear in the AST before visiting children
    fn pre_visit_hive_delimiter(&mut self, _hive_delimiter: &HiveDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive delimiter that appear in the AST after visiting children
    fn post_visit_hive_delimiter(&mut self, _hive_delimiter: &HiveDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive describe format that appear in the AST before visiting children
    fn pre_visit_hive_describe_format(&mut self, _hive_describe_format: &HiveDescribeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive describe format that appear in the AST after visiting children
    fn post_visit_hive_describe_format(&mut self, _hive_describe_format: &HiveDescribeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive distribution style that appear in the AST before visiting children
    fn pre_visit_hive_distribution_style(&mut self, _hive_distribution_style: &HiveDistributionStyle) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive distribution style that appear in the AST after visiting children
    fn post_visit_hive_distribution_style(&mut self, _hive_distribution_style: &HiveDistributionStyle) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive format that appear in the AST before visiting children
    fn pre_visit_hive_format(&mut self, _hive_format: &HiveFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive format that appear in the AST after visiting children
    fn post_visit_hive_format(&mut self, _hive_format: &HiveFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive load data format that appear in the AST before visiting children
    fn pre_visit_hive_load_data_format(&mut self, _hive_load_data_format: &HiveLoadDataFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive load data format that appear in the AST after visiting children
    fn post_visit_hive_load_data_format(&mut self, _hive_load_data_format: &HiveLoadDataFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row delimiter that appear in the AST before visiting children
    fn pre_visit_hive_row_delimiter(&mut self, _hive_row_delimiter: &HiveRowDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row delimiter that appear in the AST after visiting children
    fn post_visit_hive_row_delimiter(&mut self, _hive_row_delimiter: &HiveRowDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row format that appear in the AST before visiting children
    fn pre_visit_hive_row_format(&mut self, _hive_row_format: &HiveRowFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row format that appear in the AST after visiting children
    fn post_visit_hive_row_format(&mut self, _hive_row_format: &HiveRowFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive set location that appear in the AST before visiting children
    fn pre_visit_hive_set_location(&mut self, _hive_set_location: &HiveSetLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive set location that appear in the AST after visiting children
    fn post_visit_hive_set_location(&mut self, _hive_set_location: &HiveSetLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident that appear in the AST before visiting children
    fn pre_visit_ident(&mut self, _ident: &Ident) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident that appear in the AST after visiting children
    fn post_visit_ident(&mut self, _ident: &Ident) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident with alias that appear in the AST before visiting children
    fn pre_visit_ident_with_alias(&mut self, _ident_with_alias: &IdentWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident with alias that appear in the AST after visiting children
    fn post_visit_ident_with_alias(&mut self, _ident_with_alias: &IdentWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity parameters that appear in the AST before visiting children
    fn pre_visit_identity_parameters(&mut self, _identity_parameters: &IdentityParameters) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity parameters that appear in the AST after visiting children
    fn post_visit_identity_parameters(&mut self, _identity_parameters: &IdentityParameters) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property that appear in the AST before visiting children
    fn pre_visit_identity_property(&mut self, _identity_property: &IdentityProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property that appear in the AST after visiting children
    fn post_visit_identity_property(&mut self, _identity_property: &IdentityProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property format kind that appear in the AST before visiting children
    fn pre_visit_identity_property_format_kind(&mut self, _identity_property_format_kind: &IdentityPropertyFormatKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property format kind that appear in the AST after visiting children
    fn post_visit_identity_property_format_kind(&mut self, _identity_property_format_kind: &IdentityPropertyFormatKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property kind that appear in the AST before visiting children
    fn pre_visit_identity_property_kind(&mut self, _identity_property_kind: &IdentityPropertyKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property kind that appear in the AST after visiting children
    fn post_visit_identity_property_kind(&mut self, _identity_property_kind: &IdentityPropertyKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property order that appear in the AST before visiting children
    fn pre_visit_identity_property_order(&mut self, _identity_property_order: &IdentityPropertyOrder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property order that appear in the AST after visiting children
    fn post_visit_identity_property_order(&mut self, _identity_property_order: &IdentityPropertyOrder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any if statement that appear in the AST before visiting children
    fn pre_visit_if_statement(&mut self, _if_statement: &IfStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any if statement that appear in the AST after visiting children
    fn post_visit_if_statement(&mut self, _if_statement: &IfStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ilike select item that appear in the AST before visiting children
    fn pre_visit_ilike_select_item(&mut self, _ilike_select_item: &IlikeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ilike select item that appear in the AST after visiting children
    fn post_visit_ilike_select_item(&mut self, _ilike_select_item: &IlikeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index column that appear in the AST before visiting children
    fn pre_visit_index_column(&mut self, _index_column: &IndexColumn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index column that appear in the AST after visiting children
    fn post_visit_index_column(&mut self, _index_column: &IndexColumn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index option that appear in the AST before visiting children
    fn pre_visit_index_option(&mut self, _index_option: &IndexOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index option that appear in the AST after visiting children
    fn post_visit_index_option(&mut self, _index_option: &IndexOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index type that appear in the AST before visiting children
    fn pre_visit_index_type(&mut self, _index_type: &IndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index type that appear in the AST after visiting children
    fn post_visit_index_type(&mut self, _index_type: &IndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any input format clause that appear in the AST before visiting children
    fn pre_visit_input_format_clause(&mut self, _input_format_clause: &InputFormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any input format clause that appear in the AST after visiting children
    fn post_visit_input_format_clause(&mut self, _input_format_clause: &InputFormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert that appear in the AST before visiting children
    fn pre_visit_insert(&mut self, _insert: &Insert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert that appear in the AST after visiting children
    fn post_visit_insert(&mut self, _insert: &Insert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert aliases that appear in the AST before visiting children
    fn pre_visit_insert_aliases(&mut self, _insert_aliases: &InsertAliases) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert aliases that appear in the AST after visiting children
    fn post_visit_insert_aliases(&mut self, _insert_aliases: &InsertAliases) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate that appear in the AST before visiting children
    fn pre_visit_interpolate(&mut self, _interpolate: &Interpolate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate that appear in the AST after visiting children
    fn post_visit_interpolate(&mut self, _interpolate: &Interpolate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate expr that appear in the AST before visiting children
    fn pre_visit_interpolate_expr(&mut self, _interpolate_expr: &InterpolateExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate expr that appear in the AST after visiting children
    fn post_visit_interpolate_expr(&mut self, _interpolate_expr: &InterpolateExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interval that appear in the AST before visiting children
    fn pre_visit_interval(&mut self, _interval: &Interval) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interval that appear in the AST after visiting children
    fn post_visit_interval(&mut self, _interval: &Interval) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join that appear in the AST before visiting children
    fn pre_visit_join(&mut self, _join: &Join) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join that appear in the AST after visiting children
    fn post_visit_join(&mut self, _join: &Join) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join constraint that appear in the AST before visiting children
    fn pre_visit_join_constraint(&mut self, _join_constraint: &JoinConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join constraint that appear in the AST after visiting children
    fn post_visit_join_constraint(&mut self, _join_constraint: &JoinConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join operator that appear in the AST before visiting children
    fn pre_visit_join_operator(&mut self, _join_operator: &JoinOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join operator that appear in the AST after visiting children
    fn post_visit_join_operator(&mut self, _join_operator: &JoinOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json null clause that appear in the AST before visiting children
    fn pre_visit_json_null_clause(&mut self, _json_null_clause: &JsonNullClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json null clause that appear in the AST after visiting children
    fn post_visit_json_null_clause(&mut self, _json_null_clause: &JsonNullClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path that appear in the AST before visiting children
    fn pre_visit_json_path(&mut self, _json_path: &JsonPath) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path that appear in the AST after visiting children
    fn post_visit_json_path(&mut self, _json_path: &JsonPath) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path elem that appear in the AST before visiting children
    fn pre_visit_json_path_elem(&mut self, _json_path_elem: &JsonPathElem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path elem that appear in the AST after visiting children
    fn post_visit_json_path_elem(&mut self, _json_path_elem: &JsonPathElem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key or index display that appear in the AST before visiting children
    fn pre_visit_key_or_index_display(&mut self, _key_or_index_display: &KeyOrIndexDisplay) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key or index display that appear in the AST after visiting children
    fn post_visit_key_or_index_display(&mut self, _key_or_index_display: &KeyOrIndexDisplay) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option that appear in the AST before visiting children
    fn pre_visit_key_value_option(&mut self, _key_value_option: &KeyValueOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option that appear in the AST after visiting children
    fn post_visit_key_value_option(&mut self, _key_value_option: &KeyValueOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option type that appear in the AST before visiting children
    fn pre_visit_key_value_option_type(&mut self, _key_value_option_type: &KeyValueOptionType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option type that appear in the AST after visiting children
    fn post_visit_key_value_option_type(&mut self, _key_value_option_type: &KeyValueOptionType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value options that appear in the AST before visiting children
    fn pre_visit_key_value_options(&mut self, _key_value_options: &KeyValueOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value options that appear in the AST after visiting children
    fn post_visit_key_value_options(&mut self, _key_value_options: &KeyValueOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any kill type that appear in the AST before visiting children
    fn pre_visit_kill_type(&mut self, _kill_type: &KillType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any kill type that appear in the AST after visiting children
    fn post_visit_kill_type(&mut self, _kill_type: &KillType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lambda function that appear in the AST before visiting children
    fn pre_visit_lambda_function(&mut self, _lambda_function: &LambdaFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lambda function that appear in the AST after visiting children
    fn post_visit_lambda_function(&mut self, _lambda_function: &LambdaFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lateral view that appear in the AST before visiting children
    fn pre_visit_lateral_view(&mut self, _lateral_view: &LateralView) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lateral view that appear in the AST after visiting children
    fn post_visit_lateral_view(&mut self, _lateral_view: &LateralView) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any limit clause that appear in the AST before visiting children
    fn pre_visit_limit_clause(&mut self, _limit_clause: &LimitClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any limit clause that appear in the AST after visiting children
    fn post_visit_limit_clause(&mut self, _limit_clause: &LimitClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any list agg on overflow that appear in the AST before visiting children
    fn pre_visit_list_agg_on_overflow(&mut self, _list_agg_on_overflow: &ListAggOnOverflow) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any list agg on overflow that appear in the AST after visiting children
    fn post_visit_list_agg_on_overflow(&mut self, _list_agg_on_overflow: &ListAggOnOverflow) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any location that appear in the AST before visiting children
    fn pre_visit_location(&mut self, _location: &Location) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any location that appear in the AST after visiting children
    fn post_visit_location(&mut self, _location: &Location) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock clause that appear in the AST before visiting children
    fn pre_visit_lock_clause(&mut self, _lock_clause: &LockClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock clause that appear in the AST after visiting children
    fn post_visit_lock_clause(&mut self, _lock_clause: &LockClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table that appear in the AST before visiting children
    fn pre_visit_lock_table(&mut self, _lock_table: &LockTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table that appear in the AST after visiting children
    fn post_visit_lock_table(&mut self, _lock_table: &LockTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table type that appear in the AST before visiting children
    fn pre_visit_lock_table_type(&mut self, _lock_table_type: &LockTableType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table type that appear in the AST after visiting children
    fn post_visit_lock_table_type(&mut self, _lock_table_type: &LockTableType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock type that appear in the AST before visiting children
    fn pre_visit_lock_type(&mut self, _lock_type: &LockType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock type that appear in the AST after visiting children
    fn post_visit_lock_type(&mut self, _lock_type: &LockType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro arg that appear in the AST before visiting children
    fn pre_visit_macro_arg(&mut self, _macro_arg: &MacroArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro arg that appear in the AST after visiting children
    fn post_visit_macro_arg(&mut self, _macro_arg: &MacroArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro definition that appear in the AST before visiting children
    fn pre_visit_macro_definition(&mut self, _macro_definition: &MacroDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro definition that appear in the AST after visiting children
    fn post_visit_macro_definition(&mut self, _macro_definition: &MacroDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map that appear in the AST before visiting children
    fn pre_visit_map(&mut self, _map: &Map) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map that appear in the AST after visiting children
    fn post_visit_map(&mut self, _map: &Map) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map entry that appear in the AST before visiting children
    fn pre_visit_map_entry(&mut self, _map_entry: &MapEntry) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map entry that appear in the AST after visiting children
    fn post_visit_map_entry(&mut self, _map_entry: &MapEntry) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize pattern that appear in the AST before visiting children
    fn pre_visit_match_recognize_pattern(&mut self, _match_recognize_pattern: &MatchRecognizePattern) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize pattern that appear in the AST after visiting children
    fn post_visit_match_recognize_pattern(&mut self, _match_recognize_pattern: &MatchRecognizePattern) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize symbol that appear in the AST before visiting children
    fn pre_visit_match_recognize_symbol(&mut self, _match_recognize_symbol: &MatchRecognizeSymbol) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize symbol that appear in the AST after visiting children
    fn post_visit_match_recognize_symbol(&mut self, _match_recognize_symbol: &MatchRecognizeSymbol) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any measure that appear in the AST before visiting children
    fn pre_visit_measure(&mut self, _measure: &Measure) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any measure that appear in the AST after visiting children
    fn post_visit_measure(&mut self, _measure: &Measure) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge action that appear in the AST before visiting children
    fn pre_visit_merge_action(&mut self, _merge_action: &MergeAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge action that appear in the AST after visiting children
    fn post_visit_merge_action(&mut self, _merge_action: &MergeAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause that appear in the AST before visiting children
    fn pre_visit_merge_clause(&mut self, _merge_clause: &MergeClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause that appear in the AST after visiting children
    fn post_visit_merge_clause(&mut self, _merge_clause: &MergeClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause kind that appear in the AST before visiting children
    fn pre_visit_merge_clause_kind(&mut self, _merge_clause_kind: &MergeClauseKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause kind that appear in the AST after visiting children
    fn post_visit_merge_clause_kind(&mut self, _merge_clause_kind: &MergeClauseKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert expr that appear in the AST before visiting children
    fn pre_visit_merge_insert_expr(&mut self, _merge_insert_expr: &MergeInsertExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert expr that appear in the AST after visiting children
    fn post_visit_merge_insert_expr(&mut self, _merge_insert_expr: &MergeInsertExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert kind that appear in the AST before visiting children
    fn pre_visit_merge_insert_kind(&mut self, _merge_insert_kind: &MergeInsertKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert kind that appear in the AST after visiting children
    fn post_visit_merge_insert_kind(&mut self, _merge_insert_kind: &MergeInsertKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any method that appear in the AST before visiting children
    fn pre_visit_method(&mut self, _method: &Method) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any method that appear in the AST after visiting children
    fn post_visit_method(&mut self, _method: &Method) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any min max value that appear in the AST before visiting children
    fn pre_visit_min_max_value(&mut self, _min_max_value: &MinMaxValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any min max value that appear in the AST after visiting children
    fn post_visit_min_max_value(&mut self, _min_max_value: &MinMaxValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any my sql column position that appear in the AST before visiting children
    fn pre_visit_my_sql_column_position(&mut self, _my_sql_column_position: &MySQLColumnPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any my sql column position that appear in the AST after visiting children
    fn post_visit_my_sql_column_position(&mut self, _my_sql_column_position: &MySQLColumnPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any mysql insert priority that appear in the AST before visiting children
    fn pre_visit_mysql_insert_priority(&mut self, _mysql_insert_priority: &MysqlInsertPriority) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any mysql insert priority that appear in the AST after visiting children
    fn post_visit_mysql_insert_priority(&mut self, _mysql_insert_priority: &MysqlInsertPriority) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window definition that appear in the AST before visiting children
    fn pre_visit_named_window_definition(&mut self, _named_window_definition: &NamedWindowDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window definition that appear in the AST after visiting children
    fn post_visit_named_window_definition(&mut self, _named_window_definition: &NamedWindowDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window expr that appear in the AST before visiting children
    fn pre_visit_named_window_expr(&mut self, _named_window_expr: &NamedWindowExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window expr that appear in the AST after visiting children
    fn post_visit_named_window_expr(&mut self, _named_window_expr: &NamedWindowExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any non block that appear in the AST before visiting children
    fn pre_visit_non_block(&mut self, _non_block: &NonBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any non block that appear in the AST after visiting children
    fn post_visit_non_block(&mut self, _non_block: &NonBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any null treatment that appear in the AST before visiting children
    fn pre_visit_null_treatment(&mut self, _null_treatment: &NullTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any null treatment that appear in the AST after visiting children
    fn post_visit_null_treatment(&mut self, _null_treatment: &NullTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any nulls distinct option that appear in the AST before visiting children
    fn pre_visit_nulls_distinct_option(&mut self, _nulls_distinct_option: &NullsDistinctOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any nulls distinct option that appear in the AST after visiting children
    fn post_visit_nulls_distinct_option(&mut self, _nulls_distinct_option: &NullsDistinctOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name that appear in the AST before visiting children
    fn pre_visit_object_name(&mut self, _object_name: &ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name that appear in the AST after visiting children
    fn post_visit_object_name(&mut self, _object_name: &ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name part that appear in the AST before visiting children
    fn pre_visit_object_name_part(&mut self, _object_name_part: &ObjectNamePart) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name part that appear in the AST after visiting children
    fn post_visit_object_name_part(&mut self, _object_name_part: &ObjectNamePart) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object type that appear in the AST before visiting children
    fn pre_visit_object_type(&mut self, _object_type: &ObjectType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object type that appear in the AST after visiting children
    fn post_visit_object_type(&mut self, _object_type: &ObjectType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset that appear in the AST before visiting children
    fn pre_visit_offset(&mut self, _offset: &Offset) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset that appear in the AST after visiting children
    fn post_visit_offset(&mut self, _offset: &Offset) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset rows that appear in the AST before visiting children
    fn pre_visit_offset_rows(&mut self, _offset_rows: &OffsetRows) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset rows that appear in the AST after visiting children
    fn post_visit_offset_rows(&mut self, _offset_rows: &OffsetRows) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on commit that appear in the AST before visiting children
    fn pre_visit_on_commit(&mut self, _on_commit: &OnCommit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on commit that appear in the AST after visiting children
    fn post_visit_on_commit(&mut self, _on_commit: &OnCommit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict that appear in the AST before visiting children
    fn pre_visit_on_conflict(&mut self, _on_conflict: &OnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict that appear in the AST after visiting children
    fn post_visit_on_conflict(&mut self, _on_conflict: &OnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict action that appear in the AST before visiting children
    fn pre_visit_on_conflict_action(&mut self, _on_conflict_action: &OnConflictAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict action that appear in the AST after visiting children
    fn post_visit_on_conflict_action(&mut self, _on_conflict_action: &OnConflictAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any one or many with parens that appear in the AST before visiting children
    fn pre_visit_one_or_many_with_parens<T: Visit>(&mut self, _one_or_many_with_parens: &OneOrManyWithParens<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any one or many with parens that appear in the AST after visiting children
    fn post_visit_one_or_many_with_parens<T: Visit>(&mut self, _one_or_many_with_parens: &OneOrManyWithParens<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any operate function arg that appear in the AST before visiting children
    fn pre_visit_operate_function_arg(&mut self, _operate_function_arg: &OperateFunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any operate function arg that appear in the AST after visiting children
    fn post_visit_operate_function_arg(&mut self, _operate_function_arg: &OperateFunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by that appear in the AST before visiting children
    fn pre_visit_order_by(&mut self, _order_by: &OrderBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by that appear in the AST after visiting children
    fn post_visit_order_by(&mut self, _order_by: &OrderBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by expr that appear in the AST before visiting children
    fn pre_visit_order_by_expr(&mut self, _order_by_expr: &OrderByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by expr that appear in the AST after visiting children
    fn post_visit_order_by_expr(&mut self, _order_by_expr: &OrderByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by kind that appear in the AST before visiting children
    fn pre_visit_order_by_kind(&mut self, _order_by_kind: &OrderByKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by kind that appear in the AST after visiting children
    fn post_visit_order_by_kind(&mut self, _order_by_kind: &OrderByKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by options that appear in the AST before visiting children
    fn pre_visit_order_by_options(&mut self, _order_by_options: &OrderByOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by options that appear in the AST after visiting children
    fn post_visit_order_by_options(&mut self, _order_by_options: &OrderByOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any output clause that appear in the AST before visiting children
    fn pre_visit_output_clause(&mut self, _output_clause: &OutputClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any output clause that appear in the AST after visiting children
    fn post_visit_output_clause(&mut self, _output_clause: &OutputClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any owner that appear in the AST before visiting children
    fn pre_visit_owner(&mut self, _owner: &Owner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any owner that appear in the AST after visiting children
    fn post_visit_owner(&mut self, _owner: &Owner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition that appear in the AST before visiting children
    fn pre_visit_partition(&mut self, _partition: &Partition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition that appear in the AST after visiting children
    fn post_visit_partition(&mut self, _partition: &Partition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition range direction that appear in the AST before visiting children
    fn pre_visit_partition_range_direction(&mut self, _partition_range_direction: &PartitionRangeDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition range direction that appear in the AST after visiting children
    fn post_visit_partition_range_direction(&mut self, _partition_range_direction: &PartitionRangeDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any password that appear in the AST before visiting children
    fn pre_visit_password(&mut self, _password: &Password) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any password that appear in the AST after visiting children
    fn post_visit_password(&mut self, _password: &Password) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any pivot value source that appear in the AST before visiting children
    fn pre_visit_pivot_value_source(&mut self, _pivot_value_source: &PivotValueSource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any pivot value source that appear in the AST after visiting children
    fn post_visit_pivot_value_source(&mut self, _pivot_value_source: &PivotValueSource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any privileges that appear in the AST before visiting children
    fn pre_visit_privileges(&mut self, _privileges: &Privileges) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any privileges that appear in the AST after visiting children
    fn post_visit_privileges(&mut self, _privileges: &Privileges) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any procedure param that appear in the AST before visiting children
    fn pre_visit_procedure_param(&mut self, _procedure_param: &ProcedureParam) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any procedure param that appear in the AST after visiting children
    fn post_visit_procedure_param(&mut self, _procedure_param: &ProcedureParam) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any projection select that appear in the AST before visiting children
    fn pre_visit_projection_select(&mut self, _projection_select: &ProjectionSelect) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any projection select that appear in the AST after visiting children
    fn post_visit_projection_select(&mut self, _projection_select: &ProjectionSelect) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rais error option that appear in the AST before visiting children
    fn pre_visit_rais_error_option(&mut self, _rais_error_option: &RaisErrorOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rais error option that appear in the AST after visiting children
    fn post_visit_rais_error_option(&mut self, _rais_error_option: &RaisErrorOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement that appear in the AST before visiting children
    fn pre_visit_raise_statement(&mut self, _raise_statement: &RaiseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement that appear in the AST after visiting children
    fn post_visit_raise_statement(&mut self, _raise_statement: &RaiseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement value that appear in the AST before visiting children
    fn pre_visit_raise_statement_value(&mut self, _raise_statement_value: &RaiseStatementValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement value that appear in the AST after visiting children
    fn post_visit_raise_statement_value(&mut self, _raise_statement_value: &RaiseStatementValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any referential action that appear in the AST before visiting children
    fn pre_visit_referential_action(&mut self, _referential_action: &ReferentialAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any referential action that appear in the AST after visiting children
    fn post_visit_referential_action(&mut self, _referential_action: &ReferentialAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename select item that appear in the AST before visiting children
    fn pre_visit_rename_select_item(&mut self, _rename_select_item: &RenameSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename select item that appear in the AST after visiting children
    fn post_visit_rename_select_item(&mut self, _rename_select_item: &RenameSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename table that appear in the AST before visiting children
    fn pre_visit_rename_table(&mut self, _rename_table: &RenameTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename table that appear in the AST after visiting children
    fn post_visit_rename_table(&mut self, _rename_table: &RenameTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any repetition quantifier that appear in the AST before visiting children
    fn pre_visit_repetition_quantifier(&mut self, _repetition_quantifier: &RepetitionQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any repetition quantifier that appear in the AST after visiting children
    fn post_visit_repetition_quantifier(&mut self, _repetition_quantifier: &RepetitionQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select element that appear in the AST before visiting children
    fn pre_visit_replace_select_element(&mut self, _replace_select_element: &ReplaceSelectElement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select element that appear in the AST after visiting children
    fn post_visit_replace_select_element(&mut self, _replace_select_element: &ReplaceSelectElement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select item that appear in the AST before visiting children
    fn pre_visit_replace_select_item(&mut self, _replace_select_item: &ReplaceSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select item that appear in the AST after visiting children
    fn post_visit_replace_select_item(&mut self, _replace_select_item: &ReplaceSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any reset config that appear in the AST before visiting children
    fn pre_visit_reset_config(&mut self, _reset_config: &ResetConfig) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any reset config that appear in the AST after visiting children
    fn post_visit_reset_config(&mut self, _reset_config: &ResetConfig) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any role option that appear in the AST before visiting children
    fn pre_visit_role_option(&mut self, _role_option: &RoleOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any role option that appear in the AST after visiting children
    fn post_visit_role_option(&mut self, _role_option: &RoleOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any row access policy that appear in the AST before visiting children
    fn pre_visit_row_access_policy(&mut self, _row_access_policy: &RowAccessPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any row access policy that appear in the AST after visiting children
    fn post_visit_row_access_policy(&mut self, _row_access_policy: &RowAccessPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rows per match that appear in the AST before visiting children
    fn pre_visit_rows_per_match(&mut self, _rows_per_match: &RowsPerMatch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rows per match that appear in the AST after visiting children
    fn post_visit_rows_per_match(&mut self, _rows_per_match: &RowsPerMatch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any schema name that appear in the AST before visiting children
    fn pre_visit_schema_name(&mut self, _schema_name: &SchemaName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any schema name that appear in the AST after visiting children
    fn post_visit_schema_name(&mut self, _schema_name: &SchemaName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any search modifier that appear in the AST before visiting children
    fn pre_visit_search_modifier(&mut self, _search_modifier: &SearchModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any search modifier that appear in the AST after visiting children
    fn post_visit_search_modifier(&mut self, _search_modifier: &SearchModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secondary roles that appear in the AST before visiting children
    fn pre_visit_secondary_roles(&mut self, _secondary_roles: &SecondaryRoles) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secondary roles that appear in the AST after visiting children
    fn post_visit_secondary_roles(&mut self, _secondary_roles: &SecondaryRoles) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secret option that appear in the AST before visiting children
    fn pre_visit_secret_option(&mut self, _secret_option: &SecretOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secret option that appear in the AST after visiting children
    fn post_visit_secret_option(&mut self, _secret_option: &SecretOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select that appear in the AST before visiting children
    fn pre_visit_select(&mut self, _select: &Select) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select that appear in the AST after visiting children
    fn post_visit_select(&mut self, _select: &Select) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select flavor that appear in the AST before visiting children
    fn pre_visit_select_flavor(&mut self, _select_flavor: &SelectFlavor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select flavor that appear in the AST after visiting children
    fn post_visit_select_flavor(&mut self, _select_flavor: &SelectFlavor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select into that appear in the AST before visiting children
    fn pre_visit_select_into(&mut self, _select_into: &SelectInto) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select into that appear in the AST after visiting children
    fn post_visit_select_into(&mut self, _select_into: &SelectInto) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item that appear in the AST before visiting children
    fn pre_visit_select_item(&mut self, _select_item: &SelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item that appear in the AST after visiting children
    fn post_visit_select_item(&mut self, _select_item: &SelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item qualified wildcard kind that appear in the AST before visiting children
    fn pre_visit_select_item_qualified_wildcard_kind(&mut self, _select_item_qualified_wildcard_kind: &SelectItemQualifiedWildcardKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item qualified wildcard kind that appear in the AST after visiting children
    fn post_visit_select_item_qualified_wildcard_kind(&mut self, _select_item_qualified_wildcard_kind: &SelectItemQualifiedWildcardKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sequence options that appear in the AST before visiting children
    fn pre_visit_sequence_options(&mut self, _sequence_options: &SequenceOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sequence options that appear in the AST after visiting children
    fn post_visit_sequence_options(&mut self, _sequence_options: &SequenceOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param stats topic that appear in the AST before visiting children
    fn pre_visit_session_param_stats_topic(&mut self, _session_param_stats_topic: &SessionParamStatsTopic) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param stats topic that appear in the AST after visiting children
    fn post_visit_session_param_stats_topic(&mut self, _session_param_stats_topic: &SessionParamStatsTopic) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param value that appear in the AST before visiting children
    fn pre_visit_session_param_value(&mut self, _session_param_value: &SessionParamValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param value that appear in the AST after visiting children
    fn post_visit_session_param_value(&mut self, _session_param_value: &SessionParamValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set that appear in the AST before visiting children
    fn pre_visit_set(&mut self, _set: &Set) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set that appear in the AST after visiting children
    fn post_visit_set(&mut self, _set: &Set) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set assignment that appear in the AST before visiting children
    fn pre_visit_set_assignment(&mut self, _set_assignment: &SetAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set assignment that appear in the AST after visiting children
    fn post_visit_set_assignment(&mut self, _set_assignment: &SetAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set config value that appear in the AST before visiting children
    fn pre_visit_set_config_value(&mut self, _set_config_value: &SetConfigValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set config value that appear in the AST after visiting children
    fn post_visit_set_config_value(&mut self, _set_config_value: &SetConfigValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set expr that appear in the AST before visiting children
    fn pre_visit_set_expr(&mut self, _set_expr: &SetExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set expr that appear in the AST after visiting children
    fn post_visit_set_expr(&mut self, _set_expr: &SetExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set operator that appear in the AST before visiting children
    fn pre_visit_set_operator(&mut self, _set_operator: &SetOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set operator that appear in the AST after visiting children
    fn post_visit_set_operator(&mut self, _set_operator: &SetOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set quantifier that appear in the AST before visiting children
    fn pre_visit_set_quantifier(&mut self, _set_quantifier: &SetQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set quantifier that appear in the AST after visiting children
    fn post_visit_set_quantifier(&mut self, _set_quantifier: &SetQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table that appear in the AST before visiting children
    fn pre_visit_table(&mut self, _table: &Table) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }
    
    /// Invoked for any table that appear in the AST after visiting children
    fn post_visit_table(&mut self, _table: &Table) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param generic that appear in the AST before visiting children
    fn pre_visit_set_session_param_generic(&mut self, _set_session_param_generic: &SetSessionParamGeneric) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param generic that appear in the AST after visiting children
    fn post_visit_set_session_param_generic(&mut self, _set_session_param_generic: &SetSessionParamGeneric) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param identity insert that appear in the AST before visiting children
    fn pre_visit_set_session_param_identity_insert(&mut self, _set_session_param_identity_insert: &SetSessionParamIdentityInsert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param identity insert that appear in the AST after visiting children
    fn post_visit_set_session_param_identity_insert(&mut self, _set_session_param_identity_insert: &SetSessionParamIdentityInsert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param kind that appear in the AST before visiting children
    fn pre_visit_set_session_param_kind(&mut self, _set_session_param_kind: &SetSessionParamKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param kind that appear in the AST after visiting children
    fn post_visit_set_session_param_kind(&mut self, _set_session_param_kind: &SetSessionParamKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param offsets that appear in the AST before visiting children
    fn pre_visit_set_session_param_offsets(&mut self, _set_session_param_offsets: &SetSessionParamOffsets) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param offsets that appear in the AST after visiting children
    fn post_visit_set_session_param_offsets(&mut self, _set_session_param_offsets: &SetSessionParamOffsets) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param statistics that appear in the AST before visiting children
    fn pre_visit_set_session_param_statistics(&mut self, _set_session_param_statistics: &SetSessionParamStatistics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param statistics that appear in the AST after visiting children
    fn post_visit_set_session_param_statistics(&mut self, _set_session_param_statistics: &SetSessionParamStatistics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any setting that appear in the AST before visiting children
    fn pre_visit_setting(&mut self, _setting: &Setting) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any setting that appear in the AST after visiting children
    fn post_visit_setting(&mut self, _setting: &Setting) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show create object that appear in the AST before visiting children
    fn pre_visit_show_create_object(&mut self, _show_create_object: &ShowCreateObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show create object that appear in the AST after visiting children
    fn post_visit_show_create_object(&mut self, _show_create_object: &ShowCreateObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show objects that appear in the AST before visiting children
    fn pre_visit_show_objects(&mut self, _show_objects: &ShowObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show objects that appear in the AST after visiting children
    fn post_visit_show_objects(&mut self, _show_objects: &ShowObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter that appear in the AST before visiting children
    fn pre_visit_show_statement_filter(&mut self, _show_statement_filter: &ShowStatementFilter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter that appear in the AST after visiting children
    fn post_visit_show_statement_filter(&mut self, _show_statement_filter: &ShowStatementFilter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter position that appear in the AST before visiting children
    fn pre_visit_show_statement_filter_position(&mut self, _show_statement_filter_position: &ShowStatementFilterPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter position that appear in the AST after visiting children
    fn post_visit_show_statement_filter_position(&mut self, _show_statement_filter_position: &ShowStatementFilterPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in that appear in the AST before visiting children
    fn pre_visit_show_statement_in(&mut self, _show_statement_in: &ShowStatementIn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in that appear in the AST after visiting children
    fn post_visit_show_statement_in(&mut self, _show_statement_in: &ShowStatementIn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in clause that appear in the AST before visiting children
    fn pre_visit_show_statement_in_clause(&mut self, _show_statement_in_clause: &ShowStatementInClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in clause that appear in the AST after visiting children
    fn post_visit_show_statement_in_clause(&mut self, _show_statement_in_clause: &ShowStatementInClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in parent type that appear in the AST before visiting children
    fn pre_visit_show_statement_in_parent_type(&mut self, _show_statement_in_parent_type: &ShowStatementInParentType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in parent type that appear in the AST after visiting children
    fn post_visit_show_statement_in_parent_type(&mut self, _show_statement_in_parent_type: &ShowStatementInParentType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement options that appear in the AST before visiting children
    fn pre_visit_show_statement_options(&mut self, _show_statement_options: &ShowStatementOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement options that appear in the AST after visiting children
    fn post_visit_show_statement_options(&mut self, _show_statement_options: &ShowStatementOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any span that appear in the AST before visiting children
    fn pre_visit_span(&mut self, _span: &Span) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any span that appear in the AST after visiting children
    fn post_visit_span(&mut self, _span: &Span) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sql option that appear in the AST before visiting children
    fn pre_visit_sql_option(&mut self, _sql_option: &SqlOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sql option that appear in the AST after visiting children
    fn post_visit_sql_option(&mut self, _sql_option: &SqlOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sqlite on conflict that appear in the AST before visiting children
    fn pre_visit_sqlite_on_conflict(&mut self, _sqlite_on_conflict: &SqliteOnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sqlite on conflict that appear in the AST after visiting children
    fn post_visit_sqlite_on_conflict(&mut self, _sqlite_on_conflict: &SqliteOnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage load select item that appear in the AST before visiting children
    fn pre_visit_stage_load_select_item(&mut self, _stage_load_select_item: &StageLoadSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage load select item that appear in the AST after visiting children
    fn post_visit_stage_load_select_item(&mut self, _stage_load_select_item: &StageLoadSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage params object that appear in the AST before visiting children
    fn pre_visit_stage_params_object(&mut self, _stage_params_object: &StageParamsObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage params object that appear in the AST after visiting children
    fn post_visit_stage_params_object(&mut self, _stage_params_object: &StageParamsObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any storage serialization policy that appear in the AST before visiting children
    fn pre_visit_storage_serialization_policy(&mut self, _storage_serialization_policy: &StorageSerializationPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any storage serialization policy that appear in the AST after visiting children
    fn post_visit_storage_serialization_policy(&mut self, _storage_serialization_policy: &StorageSerializationPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct bracket kind that appear in the AST before visiting children
    fn pre_visit_struct_bracket_kind(&mut self, _struct_bracket_kind: &StructBracketKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct bracket kind that appear in the AST after visiting children
    fn post_visit_struct_bracket_kind(&mut self, _struct_bracket_kind: &StructBracketKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct field that appear in the AST before visiting children
    fn pre_visit_struct_field(&mut self, _struct_field: &StructField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct field that appear in the AST after visiting children
    fn post_visit_struct_field(&mut self, _struct_field: &StructField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any subscript that appear in the AST before visiting children
    fn pre_visit_subscript(&mut self, _subscript: &Subscript) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any subscript that appear in the AST after visiting children
    fn post_visit_subscript(&mut self, _subscript: &Subscript) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any symbol definition that appear in the AST before visiting children
    fn pre_visit_symbol_definition(&mut self, _symbol_definition: &SymbolDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any symbol definition that appear in the AST after visiting children
    fn post_visit_symbol_definition(&mut self, _symbol_definition: &SymbolDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias that appear in the AST before visiting children
    fn pre_visit_table_alias(&mut self, _table_alias: &TableAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias that appear in the AST after visiting children
    fn post_visit_table_alias(&mut self, _table_alias: &TableAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias column def that appear in the AST before visiting children
    fn pre_visit_table_alias_column_def(&mut self, _table_alias_column_def: &TableAliasColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias column def that appear in the AST after visiting children
    fn post_visit_table_alias_column_def(&mut self, _table_alias_column_def: &TableAliasColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table constraint that appear in the AST before visiting children
    fn pre_visit_table_constraint(&mut self, _table_constraint: &TableConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table constraint that appear in the AST after visiting children
    fn post_visit_table_constraint(&mut self, _table_constraint: &TableConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table engine that appear in the AST before visiting children
    fn pre_visit_table_engine(&mut self, _table_engine: &TableEngine) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table engine that appear in the AST after visiting children
    fn post_visit_table_engine(&mut self, _table_engine: &TableEngine) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table function args that appear in the AST before visiting children
    fn pre_visit_table_function_args(&mut self, _table_function_args: &TableFunctionArgs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table function args that appear in the AST after visiting children
    fn post_visit_table_function_args(&mut self, _table_function_args: &TableFunctionArgs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint for clause that appear in the AST before visiting children
    fn pre_visit_table_index_hint_for_clause(&mut self, _table_index_hint_for_clause: &TableIndexHintForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint for clause that appear in the AST after visiting children
    fn post_visit_table_index_hint_for_clause(&mut self, _table_index_hint_for_clause: &TableIndexHintForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint type that appear in the AST before visiting children
    fn pre_visit_table_index_hint_type(&mut self, _table_index_hint_type: &TableIndexHintType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint type that appear in the AST after visiting children
    fn post_visit_table_index_hint_type(&mut self, _table_index_hint_type: &TableIndexHintType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hints that appear in the AST before visiting children
    fn pre_visit_table_index_hints(&mut self, _table_index_hints: &TableIndexHints) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hints that appear in the AST after visiting children
    fn post_visit_table_index_hints(&mut self, _table_index_hints: &TableIndexHints) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index type that appear in the AST before visiting children
    fn pre_visit_table_index_type(&mut self, _table_index_type: &TableIndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index type that appear in the AST after visiting children
    fn post_visit_table_index_type(&mut self, _table_index_type: &TableIndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table object that appear in the AST before visiting children
    fn pre_visit_table_object(&mut self, _table_object: &TableObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table object that appear in the AST after visiting children
    fn post_visit_table_object(&mut self, _table_object: &TableObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table options clustered that appear in the AST before visiting children
    fn pre_visit_table_options_clustered(&mut self, _table_options_clustered: &TableOptionsClustered) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table options clustered that appear in the AST after visiting children
    fn post_visit_table_options_clustered(&mut self, _table_options_clustered: &TableOptionsClustered) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample that appear in the AST before visiting children
    fn pre_visit_table_sample(&mut self, _table_sample: &TableSample) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample that appear in the AST after visiting children
    fn post_visit_table_sample(&mut self, _table_sample: &TableSample) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample bucket that appear in the AST before visiting children
    fn pre_visit_table_sample_bucket(&mut self, _table_sample_bucket: &TableSampleBucket) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample bucket that appear in the AST after visiting children
    fn post_visit_table_sample_bucket(&mut self, _table_sample_bucket: &TableSampleBucket) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample method that appear in the AST before visiting children
    fn pre_visit_table_sample_method(&mut self, _table_sample_method: &TableSampleMethod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample method that appear in the AST after visiting children
    fn post_visit_table_sample_method(&mut self, _table_sample_method: &TableSampleMethod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample modifier that appear in the AST before visiting children
    fn pre_visit_table_sample_modifier(&mut self, _table_sample_modifier: &TableSampleModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample modifier that appear in the AST after visiting children
    fn post_visit_table_sample_modifier(&mut self, _table_sample_modifier: &TableSampleModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample quantity that appear in the AST before visiting children
    fn pre_visit_table_sample_quantity(&mut self, _table_sample_quantity: &TableSampleQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample quantity that appear in the AST after visiting children
    fn post_visit_table_sample_quantity(&mut self, _table_sample_quantity: &TableSampleQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed that appear in the AST before visiting children
    fn pre_visit_table_sample_seed(&mut self, _table_sample_seed: &TableSampleSeed) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed that appear in the AST after visiting children
    fn post_visit_table_sample_seed(&mut self, _table_sample_seed: &TableSampleSeed) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed modifier that appear in the AST before visiting children
    fn pre_visit_table_sample_seed_modifier(&mut self, _table_sample_seed_modifier: &TableSampleSeedModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed modifier that appear in the AST after visiting children
    fn post_visit_table_sample_seed_modifier(&mut self, _table_sample_seed_modifier: &TableSampleSeedModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample unit that appear in the AST before visiting children
    fn pre_visit_table_sample_unit(&mut self, _table_sample_unit: &TableSampleUnit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample unit that appear in the AST after visiting children
    fn post_visit_table_sample_unit(&mut self, _table_sample_unit: &TableSampleUnit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table version that appear in the AST before visiting children
    fn pre_visit_table_version(&mut self, _table_version: &TableVersion) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table version that appear in the AST after visiting children
    fn post_visit_table_version(&mut self, _table_version: &TableVersion) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table with joins that appear in the AST before visiting children
    fn pre_visit_table_with_joins(&mut self, _table_with_joins: &TableWithJoins) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table with joins that appear in the AST after visiting children
    fn post_visit_table_with_joins(&mut self, _table_with_joins: &TableWithJoins) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tag that appear in the AST before visiting children
    fn pre_visit_tag(&mut self, _tag: &Tag) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tag that appear in the AST after visiting children
    fn post_visit_tag(&mut self, _tag: &Tag) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tags column option that appear in the AST before visiting children
    fn pre_visit_tags_column_option(&mut self, _tags_column_option: &TagsColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tags column option that appear in the AST after visiting children
    fn post_visit_tags_column_option(&mut self, _tags_column_option: &TagsColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any timezone info that appear in the AST before visiting children
    fn pre_visit_timezone_info(&mut self, _timezone_info: &TimezoneInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any timezone info that appear in the AST after visiting children
    fn post_visit_timezone_info(&mut self, _timezone_info: &TimezoneInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token that appear in the AST before visiting children
    fn pre_visit_token(&mut self, _token: &Token) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token that appear in the AST after visiting children
    fn post_visit_token(&mut self, _token: &Token) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token with span that appear in the AST before visiting children
    fn pre_visit_token_with_span(&mut self, _token_with_span: &TokenWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token with span that appear in the AST after visiting children
    fn post_visit_token_with_span(&mut self, _token_with_span: &TokenWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top that appear in the AST before visiting children
    fn pre_visit_top(&mut self, _top: &Top) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top that appear in the AST after visiting children
    fn post_visit_top(&mut self, _top: &Top) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top quantity that appear in the AST before visiting children
    fn pre_visit_top_quantity(&mut self, _top_quantity: &TopQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top quantity that appear in the AST after visiting children
    fn post_visit_top_quantity(&mut self, _top_quantity: &TopQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction access mode that appear in the AST before visiting children
    fn pre_visit_transaction_access_mode(&mut self, _transaction_access_mode: &TransactionAccessMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction access mode that appear in the AST after visiting children
    fn post_visit_transaction_access_mode(&mut self, _transaction_access_mode: &TransactionAccessMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction isolation level that appear in the AST before visiting children
    fn pre_visit_transaction_isolation_level(&mut self, _transaction_isolation_level: &TransactionIsolationLevel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction isolation level that appear in the AST after visiting children
    fn post_visit_transaction_isolation_level(&mut self, _transaction_isolation_level: &TransactionIsolationLevel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction mode that appear in the AST before visiting children
    fn pre_visit_transaction_mode(&mut self, _transaction_mode: &TransactionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction mode that appear in the AST after visiting children
    fn post_visit_transaction_mode(&mut self, _transaction_mode: &TransactionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction modifier that appear in the AST before visiting children
    fn pre_visit_transaction_modifier(&mut self, _transaction_modifier: &TransactionModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction modifier that appear in the AST after visiting children
    fn post_visit_transaction_modifier(&mut self, _transaction_modifier: &TransactionModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger event that appear in the AST before visiting children
    fn pre_visit_trigger_event(&mut self, _trigger_event: &TriggerEvent) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger event that appear in the AST after visiting children
    fn post_visit_trigger_event(&mut self, _trigger_event: &TriggerEvent) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body that appear in the AST before visiting children
    fn pre_visit_trigger_exec_body(&mut self, _trigger_exec_body: &TriggerExecBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body that appear in the AST after visiting children
    fn post_visit_trigger_exec_body(&mut self, _trigger_exec_body: &TriggerExecBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body type that appear in the AST before visiting children
    fn pre_visit_trigger_exec_body_type(&mut self, _trigger_exec_body_type: &TriggerExecBodyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body type that appear in the AST after visiting children
    fn post_visit_trigger_exec_body_type(&mut self, _trigger_exec_body_type: &TriggerExecBodyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger object that appear in the AST before visiting children
    fn pre_visit_trigger_object(&mut self, _trigger_object: &TriggerObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger object that appear in the AST after visiting children
    fn post_visit_trigger_object(&mut self, _trigger_object: &TriggerObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger period that appear in the AST before visiting children
    fn pre_visit_trigger_period(&mut self, _trigger_period: &TriggerPeriod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger period that appear in the AST after visiting children
    fn post_visit_trigger_period(&mut self, _trigger_period: &TriggerPeriod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing that appear in the AST before visiting children
    fn pre_visit_trigger_referencing(&mut self, _trigger_referencing: &TriggerReferencing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing that appear in the AST after visiting children
    fn post_visit_trigger_referencing(&mut self, _trigger_referencing: &TriggerReferencing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing type that appear in the AST before visiting children
    fn pre_visit_trigger_referencing_type(&mut self, _trigger_referencing_type: &TriggerReferencingType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing type that appear in the AST after visiting children
    fn post_visit_trigger_referencing_type(&mut self, _trigger_referencing_type: &TriggerReferencingType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trim where field that appear in the AST before visiting children
    fn pre_visit_trim_where_field(&mut self, _trim_where_field: &TrimWhereField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trim where field that appear in the AST after visiting children
    fn post_visit_trim_where_field(&mut self, _trim_where_field: &TrimWhereField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any truncate identity option that appear in the AST before visiting children
    fn pre_visit_truncate_identity_option(&mut self, _truncate_identity_option: &TruncateIdentityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any truncate identity option that appear in the AST after visiting children
    fn post_visit_truncate_identity_option(&mut self, _truncate_identity_option: &TruncateIdentityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any unary operator that appear in the AST before visiting children
    fn pre_visit_unary_operator(&mut self, _unary_operator: &UnaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any unary operator that appear in the AST after visiting children
    fn post_visit_unary_operator(&mut self, _unary_operator: &UnaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any union field that appear in the AST before visiting children
    fn pre_visit_union_field(&mut self, _union_field: &UnionField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any union field that appear in the AST after visiting children
    fn post_visit_union_field(&mut self, _union_field: &UnionField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any update table from kind that appear in the AST before visiting children
    fn pre_visit_update_table_from_kind(&mut self, _update_table_from_kind: &UpdateTableFromKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any update table from kind that appear in the AST after visiting children
    fn post_visit_update_table_from_kind(&mut self, _update_table_from_kind: &UpdateTableFromKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any use that appear in the AST before visiting children
    fn pre_visit_use(&mut self, _use: &Use) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any use that appear in the AST after visiting children
    fn post_visit_use(&mut self, _use: &Use) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type composite attribute def that appear in the AST before visiting children
    fn pre_visit_user_defined_type_composite_attribute_def(&mut self, _user_defined_type_composite_attribute_def: &UserDefinedTypeCompositeAttributeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type composite attribute def that appear in the AST after visiting children
    fn post_visit_user_defined_type_composite_attribute_def(&mut self, _user_defined_type_composite_attribute_def: &UserDefinedTypeCompositeAttributeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type representation that appear in the AST before visiting children
    fn pre_visit_user_defined_type_representation(&mut self, _user_defined_type_representation: &UserDefinedTypeRepresentation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type representation that appear in the AST after visiting children
    fn post_visit_user_defined_type_representation(&mut self, _user_defined_type_representation: &UserDefinedTypeRepresentation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any utility option that appear in the AST before visiting children
    fn pre_visit_utility_option(&mut self, _utility_option: &UtilityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any utility option that appear in the AST after visiting children
    fn post_visit_utility_option(&mut self, _utility_option: &UtilityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value table mode that appear in the AST before visiting children
    fn pre_visit_value_table_mode(&mut self, _value_table_mode: &ValueTableMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value table mode that appear in the AST after visiting children
    fn post_visit_value_table_mode(&mut self, _value_table_mode: &ValueTableMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value with span that appear in the AST before visiting children
    fn pre_visit_value_with_span(&mut self, _value_with_span: &ValueWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value with span that appear in the AST after visiting children
    fn post_visit_value_with_span(&mut self, _value_with_span: &ValueWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any values that appear in the AST before visiting children
    fn pre_visit_values(&mut self, _values: &Values) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any values that appear in the AST after visiting children
    fn post_visit_values(&mut self, _values: &Values) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any view column def that appear in the AST before visiting children
    fn pre_visit_view_column_def(&mut self, _view_column_def: &ViewColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any view column def that appear in the AST after visiting children
    fn post_visit_view_column_def(&mut self, _view_column_def: &ViewColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any whitespace that appear in the AST before visiting children
    fn pre_visit_whitespace(&mut self, _whitespace: &Whitespace) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any whitespace that appear in the AST after visiting children
    fn post_visit_whitespace(&mut self, _whitespace: &Whitespace) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wildcard additional options that appear in the AST before visiting children
    fn pre_visit_wildcard_additional_options(&mut self, _wildcard_additional_options: &WildcardAdditionalOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wildcard additional options that appear in the AST after visiting children
    fn post_visit_wildcard_additional_options(&mut self, _wildcard_additional_options: &WildcardAdditionalOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame that appear in the AST before visiting children
    fn pre_visit_window_frame(&mut self, _window_frame: &WindowFrame) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame that appear in the AST after visiting children
    fn post_visit_window_frame(&mut self, _window_frame: &WindowFrame) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame bound that appear in the AST before visiting children
    fn pre_visit_window_frame_bound(&mut self, _window_frame_bound: &WindowFrameBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame bound that appear in the AST after visiting children
    fn post_visit_window_frame_bound(&mut self, _window_frame_bound: &WindowFrameBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame units that appear in the AST before visiting children
    fn pre_visit_window_frame_units(&mut self, _window_frame_units: &WindowFrameUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame units that appear in the AST after visiting children
    fn post_visit_window_frame_units(&mut self, _window_frame_units: &WindowFrameUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window spec that appear in the AST before visiting children
    fn pre_visit_window_spec(&mut self, _window_spec: &WindowSpec) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window spec that appear in the AST after visiting children
    fn post_visit_window_spec(&mut self, _window_spec: &WindowSpec) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window type that appear in the AST before visiting children
    fn pre_visit_window_type(&mut self, _window_type: &WindowType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window type that appear in the AST after visiting children
    fn post_visit_window_type(&mut self, _window_type: &WindowType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with that appear in the AST before visiting children
    fn pre_visit_with(&mut self, _with: &With) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with that appear in the AST after visiting children
    fn post_visit_with(&mut self, _with: &With) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with fill that appear in the AST before visiting children
    fn pre_visit_with_fill(&mut self, _with_fill: &WithFill) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with fill that appear in the AST after visiting children
    fn post_visit_with_fill(&mut self, _with_fill: &WithFill) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any word that appear in the AST before visiting children
    fn pre_visit_word(&mut self, _word: &Word) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any word that appear in the AST after visiting children
    fn post_visit_word(&mut self, _word: &Word) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wrapped collection that appear in the AST before visiting children
    fn pre_visit_wrapped_collection<T: Visit>(&mut self, _wrapped_collection: &WrappedCollection<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wrapped collection that appear in the AST after visiting children
    fn post_visit_wrapped_collection<T: Visit>(&mut self, _wrapped_collection: &WrappedCollection<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }
}

/// A visitor that can be used to mutate an AST tree.
///
/// `pre_visit_` methods are invoked before visiting all children of the
/// node and `post_visit_` methods are invoked after visiting all
/// children of the node.
///
/// # See also
///
/// These methods provide a more concise way of visiting nodes of a certain type:
/// * [visit_relations_mut]
/// * [visit_expressions_mut]
/// * [visit_statements_mut]
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{VisitMut, VisitorMut, ObjectName, Expr, Ident};
/// # use core::ops::ControlFlow;
///
/// // A visitor that replaces "to_replace" with "replaced" in all expressions
/// struct Replacer;
///
/// // Visit each expression after its children have been visited
/// impl VisitorMut for Replacer {
///   type Break = ();
///
///   fn post_visit_expr(&mut self, expr: &mut Expr) -> ControlFlow<Self::Break> {
///     if let Expr::Identifier(Ident{ value, ..}) = expr {
///         *value = value.replace("to_replace", "replaced")
///     }
///     ControlFlow::Continue(())
///   }
/// }
///
/// let sql = "SELECT to_replace FROM foo where to_replace IN (SELECT to_replace FROM bar)";
/// let mut statements = Parser::parse_sql(&GenericDialect{}, sql).unwrap();
///
/// // Drive the visitor through the AST
/// statements.visit(&mut Replacer);
///
/// assert_eq!(statements[0].to_string(), "SELECT replaced FROM foo WHERE replaced IN (SELECT replaced FROM bar)");
/// ```
pub trait VisitorMut {
    /// Type returned when the recursion returns early.
    type Break;

    /// Invoked for any queries that appear in the AST before visiting children
    fn pre_visit_query(&mut self, _query: &mut Query) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any queries that appear in the AST after visiting children
    fn post_visit_query(&mut self, _query: &mut Query) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any relations (e.g. tables) that appear in the AST before visiting children
    fn pre_visit_relation(&mut self, _relation: &mut ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any relations (e.g. tables) that appear in the AST after visiting children
    fn post_visit_relation(&mut self, _relation: &mut ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table factors that appear in the AST before visiting children
    fn pre_visit_table_factor(&mut self, _table_factor: &mut TableFactor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table factors that appear in the AST after visiting children
    fn post_visit_table_factor(&mut self, _table_factor: &mut TableFactor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expressions that appear in the AST before visiting children
    fn pre_visit_expr(&mut self, _expr: &mut Expr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expressions that appear in the AST
    fn post_visit_expr(&mut self, _expr: &mut Expr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any statements that appear in the AST before visiting children
    fn pre_visit_statement(&mut self, _statement: &mut Statement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any statements that appear in the AST after visiting children
    fn post_visit_statement(&mut self, _statement: &mut Statement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value that appear in the AST before visiting children
    fn pre_visit_value(&mut self, _value: &mut Value) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any statements that appear in the AST after visiting children
    fn post_visit_value(&mut self, _value: &mut Value) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any access expr that appear in the AST before visiting children
    fn pre_visit_access_expr(&mut self, _access_expr: &mut AccessExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any access expr that appear in the AST after visiting children
    fn post_visit_access_expr(&mut self, _access_expr: &mut AccessExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any action that appear in the AST before visiting children
    fn pre_visit_action(&mut self, _action: &mut Action) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any action that appear in the AST after visiting children
    fn post_visit_action(&mut self, _action: &mut Action) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any add drop sync that appear in the AST before visiting children
    fn pre_visit_add_drop_sync(&mut self, _add_drop_sync: &mut AddDropSync) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any add drop sync that appear in the AST after visiting children
    fn post_visit_add_drop_sync(&mut self, _add_drop_sync: &mut AddDropSync) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any after match skip that appear in the AST before visiting children
    fn pre_visit_after_match_skip(&mut self, _after_match_skip: &mut AfterMatchSkip) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any after match skip that appear in the AST after visiting children
    fn post_visit_after_match_skip(&mut self, _after_match_skip: &mut AfterMatchSkip) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter column operation that appear in the AST before visiting children
    fn pre_visit_alter_column_operation(&mut self, _alter_column_operation: &mut AlterColumnOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter column operation that appear in the AST after visiting children
    fn post_visit_alter_column_operation(&mut self, _alter_column_operation: &mut AlterColumnOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter connector owner that appear in the AST before visiting children
    fn pre_visit_alter_connector_owner(&mut self, _alter_connector_owner: &mut AlterConnectorOwner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter connector owner that appear in the AST after visiting children
    fn post_visit_alter_connector_owner(&mut self, _alter_connector_owner: &mut AlterConnectorOwner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter index operation that appear in the AST before visiting children
    fn pre_visit_alter_index_operation(&mut self, _alter_index_operation: &mut AlterIndexOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter index operation that appear in the AST after visiting children
    fn post_visit_alter_index_operation(&mut self, _alter_index_operation: &mut AlterIndexOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter policy operation that appear in the AST before visiting children
    fn pre_visit_alter_policy_operation(&mut self, _alter_policy_operation: &mut AlterPolicyOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter policy operation that appear in the AST after visiting children
    fn post_visit_alter_policy_operation(&mut self, _alter_policy_operation: &mut AlterPolicyOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter role operation that appear in the AST before visiting children
    fn pre_visit_alter_role_operation(&mut self, _alter_role_operation: &mut AlterRoleOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter role operation that appear in the AST after visiting children
    fn post_visit_alter_role_operation(&mut self, _alter_role_operation: &mut AlterRoleOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table algorithm that appear in the AST before visiting children
    fn pre_visit_alter_table_algorithm(&mut self, _alter_table_algorithm: &mut AlterTableAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table algorithm that appear in the AST after visiting children
    fn post_visit_alter_table_algorithm(&mut self, _alter_table_algorithm: &mut AlterTableAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table lock that appear in the AST before visiting children
    fn pre_visit_alter_table_lock(&mut self, _alter_table_lock: &mut AlterTableLock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table lock that appear in the AST after visiting children
    fn post_visit_alter_table_lock(&mut self, _alter_table_lock: &mut AlterTableLock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table operation that appear in the AST before visiting children
    fn pre_visit_alter_table_operation(&mut self, _alter_table_operation: &mut AlterTableOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter table operation that appear in the AST after visiting children
    fn post_visit_alter_table_operation(&mut self, _alter_table_operation: &mut AlterTableOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type that appear in the AST before visiting children
    fn pre_visit_alter_type(&mut self, _alter_type: &mut AlterType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type that appear in the AST after visiting children
    fn post_visit_alter_type(&mut self, _alter_type: &mut AlterType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value that appear in the AST before visiting children
    fn pre_visit_alter_type_add_value(&mut self, _alter_type_add_value: &mut AlterTypeAddValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value that appear in the AST after visiting children
    fn post_visit_alter_type_add_value(&mut self, _alter_type_add_value: &mut AlterTypeAddValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value position that appear in the AST before visiting children
    fn pre_visit_alter_type_add_value_position(&mut self, _alter_type_add_value_position: &mut AlterTypeAddValuePosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type add value position that appear in the AST after visiting children
    fn post_visit_alter_type_add_value_position(&mut self, _alter_type_add_value_position: &mut AlterTypeAddValuePosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type operation that appear in the AST before visiting children
    fn pre_visit_alter_type_operation(&mut self, _alter_type_operation: &mut AlterTypeOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type operation that appear in the AST after visiting children
    fn post_visit_alter_type_operation(&mut self, _alter_type_operation: &mut AlterTypeOperation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename that appear in the AST before visiting children
    fn pre_visit_alter_type_rename(&mut self, _alter_type_rename: &mut AlterTypeRename) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename that appear in the AST after visiting children
    fn post_visit_alter_type_rename(&mut self, _alter_type_rename: &mut AlterTypeRename) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename value that appear in the AST before visiting children
    fn pre_visit_alter_type_rename_value(&mut self, _alter_type_rename_value: &mut AlterTypeRenameValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any alter type rename value that appear in the AST after visiting children
    fn post_visit_alter_type_rename_value(&mut self, _alter_type_rename_value: &mut AlterTypeRenameValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any analyze format that appear in the AST before visiting children
    fn pre_visit_analyze_format(&mut self, _analyze_format: &mut AnalyzeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any analyze format that appear in the AST after visiting children
    fn post_visit_analyze_format(&mut self, _analyze_format: &mut AnalyzeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any arg mode that appear in the AST before visiting children
    fn pre_visit_arg_mode(&mut self, _arg_mode: &mut ArgMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any arg mode that appear in the AST after visiting children
    fn post_visit_arg_mode(&mut self, _arg_mode: &mut ArgMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array that appear in the AST before visiting children
    fn pre_visit_array(&mut self, _array: &mut Array) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array that appear in the AST after visiting children
    fn post_visit_array(&mut self, _array: &mut Array) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array elem type def that appear in the AST before visiting children
    fn pre_visit_array_elem_type_def(&mut self, _array_elem_type_def: &mut ArrayElemTypeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any array elem type def that appear in the AST after visiting children
    fn post_visit_array_elem_type_def(&mut self, _array_elem_type_def: &mut ArrayElemTypeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment that appear in the AST before visiting children
    fn pre_visit_assignment(&mut self, _assignment: &mut Assignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment that appear in the AST after visiting children
    fn post_visit_assignment(&mut self, _assignment: &mut Assignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment target that appear in the AST before visiting children
    fn pre_visit_assignment_target(&mut self, _assignment_target: &mut AssignmentTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any assignment target that appear in the AST after visiting children
    fn post_visit_assignment_target(&mut self, _assignment_target: &mut AssignmentTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attach duck db database option that appear in the AST before visiting children
    fn pre_visit_attach_duck_db_database_option(&mut self, _attach_duck_db_database_option: &mut AttachDuckDBDatabaseOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attach duck db database option that appear in the AST after visiting children
    fn post_visit_attach_duck_db_database_option(&mut self, _attach_duck_db_database_option: &mut AttachDuckDBDatabaseOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attached token that appear in the AST before visiting children
    fn pre_visit_attached_token(&mut self, _attached_token: &mut AttachedToken) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any attached token that appear in the AST after visiting children
    fn post_visit_attached_token(&mut self, _attached_token: &mut AttachedToken) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any begin transaction kind that appear in the AST before visiting children
    fn pre_visit_begin_transaction_kind(&mut self, _begin_transaction_kind: &mut BeginTransactionKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any begin transaction kind that appear in the AST after visiting children
    fn post_visit_begin_transaction_kind(&mut self, _begin_transaction_kind: &mut BeginTransactionKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary length that appear in the AST before visiting children
    fn pre_visit_binary_length(&mut self, _binary_length: &mut BinaryLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary length that appear in the AST after visiting children
    fn post_visit_binary_length(&mut self, _binary_length: &mut BinaryLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary operator that appear in the AST before visiting children
    fn pre_visit_binary_operator(&mut self, _binary_operator: &mut BinaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any binary operator that appear in the AST after visiting children
    fn post_visit_binary_operator(&mut self, _binary_operator: &mut BinaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cascade option that appear in the AST before visiting children
    fn pre_visit_cascade_option(&mut self, _cascade_option: &mut CascadeOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cascade option that appear in the AST after visiting children
    fn post_visit_cascade_option(&mut self, _cascade_option: &mut CascadeOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case statement that appear in the AST before visiting children
    fn pre_visit_case_statement(&mut self, _case_statement: &mut CaseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case statement that appear in the AST after visiting children
    fn post_visit_case_statement(&mut self, _case_statement: &mut CaseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case when that appear in the AST before visiting children
    fn pre_visit_case_when(&mut self, _case_when: &mut CaseWhen) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any case when that appear in the AST after visiting children
    fn post_visit_case_when(&mut self, _case_when: &mut CaseWhen) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast format that appear in the AST before visiting children
    fn pre_visit_cast_format(&mut self, _cast_format: &mut CastFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast format that appear in the AST after visiting children
    fn post_visit_cast_format(&mut self, _cast_format: &mut CastFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast kind that appear in the AST before visiting children
    fn pre_visit_cast_kind(&mut self, _cast_kind: &mut CastKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cast kind that appear in the AST after visiting children
    fn post_visit_cast_kind(&mut self, _cast_kind: &mut CastKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ceil floor kind that appear in the AST before visiting children
    fn pre_visit_ceil_floor_kind(&mut self, _ceil_floor_kind: &mut CeilFloorKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ceil floor kind that appear in the AST after visiting children
    fn post_visit_ceil_floor_kind(&mut self, _ceil_floor_kind: &mut CeilFloorKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any char length units that appear in the AST before visiting children
    fn pre_visit_char_length_units(&mut self, _char_length_units: &mut CharLengthUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any char length units that appear in the AST after visiting children
    fn post_visit_char_length_units(&mut self, _char_length_units: &mut CharLengthUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any character length that appear in the AST before visiting children
    fn pre_visit_character_length(&mut self, _character_length: &mut CharacterLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any character length that appear in the AST after visiting children
    fn post_visit_character_length(&mut self, _character_length: &mut CharacterLength) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any close cursor that appear in the AST before visiting children
    fn pre_visit_close_cursor(&mut self, _close_cursor: &mut CloseCursor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any close cursor that appear in the AST after visiting children
    fn post_visit_close_cursor(&mut self, _close_cursor: &mut CloseCursor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered by that appear in the AST before visiting children
    fn pre_visit_clustered_by(&mut self, _clustered_by: &mut ClusteredBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered by that appear in the AST after visiting children
    fn post_visit_clustered_by(&mut self, _clustered_by: &mut ClusteredBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered index that appear in the AST before visiting children
    fn pre_visit_clustered_index(&mut self, _clustered_index: &mut ClusteredIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any clustered index that appear in the AST after visiting children
    fn post_visit_clustered_index(&mut self, _clustered_index: &mut ClusteredIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column def that appear in the AST before visiting children
    fn pre_visit_column_def(&mut self, _column_def: &mut ColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column def that appear in the AST after visiting children
    fn post_visit_column_def(&mut self, _column_def: &mut ColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option that appear in the AST before visiting children
    fn pre_visit_column_option(&mut self, _column_option: &mut ColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option that appear in the AST after visiting children
    fn post_visit_column_option(&mut self, _column_option: &mut ColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option def that appear in the AST before visiting children
    fn pre_visit_column_option_def(&mut self, _column_option_def: &mut ColumnOptionDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column option def that appear in the AST after visiting children
    fn post_visit_column_option_def(&mut self, _column_option_def: &mut ColumnOptionDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy that appear in the AST before visiting children
    fn pre_visit_column_policy(&mut self, _column_policy: &mut ColumnPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy that appear in the AST after visiting children
    fn post_visit_column_policy(&mut self, _column_policy: &mut ColumnPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy property that appear in the AST before visiting children
    fn pre_visit_column_policy_property(&mut self, _column_policy_property: &mut ColumnPolicyProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any column policy property that appear in the AST after visiting children
    fn post_visit_column_policy_property(&mut self, _column_policy_property: &mut ColumnPolicyProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment def that appear in the AST before visiting children
    fn pre_visit_comment_def(&mut self, _comment_def: &mut CommentDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment def that appear in the AST after visiting children
    fn post_visit_comment_def(&mut self, _comment_def: &mut CommentDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment object that appear in the AST before visiting children
    fn pre_visit_comment_object(&mut self, _comment_object: &mut CommentObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any comment object that appear in the AST after visiting children
    fn post_visit_comment_object(&mut self, _comment_object: &mut CommentObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statement block that appear in the AST before visiting children
    fn pre_visit_conditional_statement_block(&mut self, _conditional_statement_block: &mut ConditionalStatementBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statement block that appear in the AST after visiting children
    fn post_visit_conditional_statement_block(&mut self, _conditional_statement_block: &mut ConditionalStatementBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statements that appear in the AST before visiting children
    fn pre_visit_conditional_statements(&mut self, _conditional_statements: &mut ConditionalStatements) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conditional statements that appear in the AST after visiting children
    fn post_visit_conditional_statements(&mut self, _conditional_statements: &mut ConditionalStatements) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conflict target that appear in the AST before visiting children
    fn pre_visit_conflict_target(&mut self, _conflict_target: &mut ConflictTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any conflict target that appear in the AST after visiting children
    fn post_visit_conflict_target(&mut self, _conflict_target: &mut ConflictTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any connect by that appear in the AST before visiting children
    fn pre_visit_connect_by(&mut self, _connect_by: &mut ConnectBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any connect by that appear in the AST after visiting children
    fn post_visit_connect_by(&mut self, _connect_by: &mut ConnectBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any constraint characteristics that appear in the AST before visiting children
    fn pre_visit_constraint_characteristics(&mut self, _constraint_characteristics: &mut ConstraintCharacteristics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any constraint characteristics that appear in the AST after visiting children
    fn post_visit_constraint_characteristics(&mut self, _constraint_characteristics: &mut ConstraintCharacteristics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any context modifier that appear in the AST before visiting children
    fn pre_visit_context_modifier(&mut self, _context_modifier: &mut ContextModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any context modifier that appear in the AST after visiting children
    fn post_visit_context_modifier(&mut self, _context_modifier: &mut ContextModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy into snowflake kind that appear in the AST before visiting children
    fn pre_visit_copy_into_snowflake_kind(&mut self, _copy_into_snowflake_kind: &mut CopyIntoSnowflakeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy into snowflake kind that appear in the AST after visiting children
    fn post_visit_copy_into_snowflake_kind(&mut self, _copy_into_snowflake_kind: &mut CopyIntoSnowflakeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy csv option that appear in the AST before visiting children
    fn pre_visit_copy_legacy_csv_option(&mut self, _copy_legacy_csv_option: &mut CopyLegacyCsvOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy csv option that appear in the AST after visiting children
    fn post_visit_copy_legacy_csv_option(&mut self, _copy_legacy_csv_option: &mut CopyLegacyCsvOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy option that appear in the AST before visiting children
    fn pre_visit_copy_legacy_option(&mut self, _copy_legacy_option: &mut CopyLegacyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy legacy option that appear in the AST after visiting children
    fn post_visit_copy_legacy_option(&mut self, _copy_legacy_option: &mut CopyLegacyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy option that appear in the AST before visiting children
    fn pre_visit_copy_option(&mut self, _copy_option: &mut CopyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy option that appear in the AST after visiting children
    fn post_visit_copy_option(&mut self, _copy_option: &mut CopyOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy source that appear in the AST before visiting children
    fn pre_visit_copy_source(&mut self, _copy_source: &mut CopySource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy source that appear in the AST after visiting children
    fn post_visit_copy_source(&mut self, _copy_source: &mut CopySource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy target that appear in the AST before visiting children
    fn pre_visit_copy_target(&mut self, _copy_target: &mut CopyTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any copy target that appear in the AST after visiting children
    fn post_visit_copy_target(&mut self, _copy_target: &mut CopyTarget) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create connector that appear in the AST before visiting children
    fn pre_visit_create_connector(&mut self, _create_connector: &mut CreateConnector) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create connector that appear in the AST after visiting children
    fn post_visit_create_connector(&mut self, _create_connector: &mut CreateConnector) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function that appear in the AST before visiting children
    fn pre_visit_create_function(&mut self, _create_function: &mut CreateFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function that appear in the AST after visiting children
    fn post_visit_create_function(&mut self, _create_function: &mut CreateFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function body that appear in the AST before visiting children
    fn pre_visit_create_function_body(&mut self, _create_function_body: &mut CreateFunctionBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function body that appear in the AST after visiting children
    fn post_visit_create_function_body(&mut self, _create_function_body: &mut CreateFunctionBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function using that appear in the AST before visiting children
    fn pre_visit_create_function_using(&mut self, _create_function_using: &mut CreateFunctionUsing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create function using that appear in the AST after visiting children
    fn post_visit_create_function_using(&mut self, _create_function_using: &mut CreateFunctionUsing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create index that appear in the AST before visiting children
    fn pre_visit_create_index(&mut self, _create_index: &mut CreateIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create index that appear in the AST after visiting children
    fn post_visit_create_index(&mut self, _create_index: &mut CreateIndex) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy command that appear in the AST before visiting children
    fn pre_visit_create_policy_command(&mut self, _create_policy_command: &mut CreatePolicyCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy command that appear in the AST after visiting children
    fn post_visit_create_policy_command(&mut self, _create_policy_command: &mut CreatePolicyCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy type that appear in the AST before visiting children
    fn pre_visit_create_policy_type(&mut self, _create_policy_type: &mut CreatePolicyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create policy type that appear in the AST after visiting children
    fn post_visit_create_policy_type(&mut self, _create_policy_type: &mut CreatePolicyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table that appear in the AST before visiting children
    fn pre_visit_create_table(&mut self, _create_table: &mut CreateTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table that appear in the AST after visiting children
    fn post_visit_create_table(&mut self, _create_table: &mut CreateTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table builder that appear in the AST before visiting children
    fn pre_visit_create_table_builder(&mut self, _create_table_builder: &mut CreateTableBuilder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table builder that appear in the AST after visiting children
    fn post_visit_create_table_builder(&mut self, _create_table_builder: &mut CreateTableBuilder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table options that appear in the AST before visiting children
    fn pre_visit_create_table_options(&mut self, _create_table_options: &mut CreateTableOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create table options that appear in the AST after visiting children
    fn post_visit_create_table_options(&mut self, _create_table_options: &mut CreateTableOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view algorithm that appear in the AST before visiting children
    fn pre_visit_create_view_algorithm(&mut self, _create_view_algorithm: &mut CreateViewAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view algorithm that appear in the AST after visiting children
    fn post_visit_create_view_algorithm(&mut self, _create_view_algorithm: &mut CreateViewAlgorithm) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view params that appear in the AST before visiting children
    fn pre_visit_create_view_params(&mut self, _create_view_params: &mut CreateViewParams) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view params that appear in the AST after visiting children
    fn post_visit_create_view_params(&mut self, _create_view_params: &mut CreateViewParams) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view security that appear in the AST before visiting children
    fn pre_visit_create_view_security(&mut self, _create_view_security: &mut CreateViewSecurity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any create view security that appear in the AST after visiting children
    fn post_visit_create_view_security(&mut self, _create_view_security: &mut CreateViewSecurity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte that appear in the AST before visiting children
    fn pre_visit_cte(&mut self, _cte: &mut Cte) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte that appear in the AST after visiting children
    fn post_visit_cte(&mut self, _cte: &mut Cte) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte as materialized that appear in the AST before visiting children
    fn pre_visit_cte_as_materialized(&mut self, _cte_as_materialized: &mut CteAsMaterialized) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any cte as materialized that appear in the AST after visiting children
    fn post_visit_cte_as_materialized(&mut self, _cte_as_materialized: &mut CteAsMaterialized) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any data type that appear in the AST before visiting children
    fn pre_visit_data_type(&mut self, _data_type: &mut DataType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any data type that appear in the AST after visiting children
    fn post_visit_data_type(&mut self, _data_type: &mut DataType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any date time field that appear in the AST before visiting children
    fn pre_visit_date_time_field(&mut self, _date_time_field: &mut DateTimeField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any date time field that appear in the AST after visiting children
    fn post_visit_date_time_field(&mut self, _date_time_field: &mut DateTimeField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare that appear in the AST before visiting children
    fn pre_visit_declare(&mut self, _declare: &mut Declare) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare that appear in the AST after visiting children
    fn post_visit_declare(&mut self, _declare: &mut Declare) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare assignment that appear in the AST before visiting children
    fn pre_visit_declare_assignment(&mut self, _declare_assignment: &mut DeclareAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare assignment that appear in the AST after visiting children
    fn post_visit_declare_assignment(&mut self, _declare_assignment: &mut DeclareAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare type that appear in the AST before visiting children
    fn pre_visit_declare_type(&mut self, _declare_type: &mut DeclareType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any declare type that appear in the AST after visiting children
    fn post_visit_declare_type(&mut self, _declare_type: &mut DeclareType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deduplicate that appear in the AST before visiting children
    fn pre_visit_deduplicate(&mut self, _deduplicate: &mut Deduplicate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deduplicate that appear in the AST after visiting children
    fn post_visit_deduplicate(&mut self, _deduplicate: &mut Deduplicate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deferrable initial that appear in the AST before visiting children
    fn pre_visit_deferrable_initial(&mut self, _deferrable_initial: &mut DeferrableInitial) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any deferrable initial that appear in the AST after visiting children
    fn post_visit_deferrable_initial(&mut self, _deferrable_initial: &mut DeferrableInitial) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any delete that appear in the AST before visiting children
    fn pre_visit_delete(&mut self, _delete: &mut Delete) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any delete that appear in the AST after visiting children
    fn post_visit_delete(&mut self, _delete: &mut Delete) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any describe alias that appear in the AST before visiting children
    fn pre_visit_describe_alias(&mut self, _describe_alias: &mut DescribeAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any describe alias that appear in the AST after visiting children
    fn post_visit_describe_alias(&mut self, _describe_alias: &mut DescribeAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dictionary field that appear in the AST before visiting children
    fn pre_visit_dictionary_field(&mut self, _dictionary_field: &mut DictionaryField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dictionary field that appear in the AST after visiting children
    fn post_visit_dictionary_field(&mut self, _dictionary_field: &mut DictionaryField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any discard object that appear in the AST before visiting children
    fn pre_visit_discard_object(&mut self, _discard_object: &mut DiscardObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any discard object that appear in the AST after visiting children
    fn post_visit_discard_object(&mut self, _discard_object: &mut DiscardObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any distinct that appear in the AST before visiting children
    fn pre_visit_distinct(&mut self, _distinct: &mut Distinct) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any distinct that appear in the AST after visiting children
    fn post_visit_distinct(&mut self, _distinct: &mut Distinct) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any do update that appear in the AST before visiting children
    fn pre_visit_do_update(&mut self, _do_update: &mut DoUpdate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any do update that appear in the AST after visiting children
    fn post_visit_do_update(&mut self, _do_update: &mut DoUpdate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dollar quoted string that appear in the AST before visiting children
    fn pre_visit_dollar_quoted_string(&mut self, _dollar_quoted_string: &mut DollarQuotedString) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any dollar quoted string that appear in the AST after visiting children
    fn post_visit_dollar_quoted_string(&mut self, _dollar_quoted_string: &mut DollarQuotedString) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any drop behavior that appear in the AST before visiting children
    fn pre_visit_drop_behavior(&mut self, _drop_behavior: &mut DropBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any drop behavior that appear in the AST after visiting children
    fn post_visit_drop_behavior(&mut self, _drop_behavior: &mut DropBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any duplicate treatment that appear in the AST before visiting children
    fn pre_visit_duplicate_treatment(&mut self, _duplicate_treatment: &mut DuplicateTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any duplicate treatment that appear in the AST after visiting children
    fn post_visit_duplicate_treatment(&mut self, _duplicate_treatment: &mut DuplicateTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any empty matches mode that appear in the AST before visiting children
    fn pre_visit_empty_matches_mode(&mut self, _empty_matches_mode: &mut EmptyMatchesMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any empty matches mode that appear in the AST after visiting children
    fn post_visit_empty_matches_mode(&mut self, _empty_matches_mode: &mut EmptyMatchesMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any enum member that appear in the AST before visiting children
    fn pre_visit_enum_member(&mut self, _enum_member: &mut EnumMember) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any enum member that appear in the AST after visiting children
    fn post_visit_enum_member(&mut self, _enum_member: &mut EnumMember) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exact number info that appear in the AST before visiting children
    fn pre_visit_exact_number_info(&mut self, _exact_number_info: &mut ExactNumberInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exact number info that appear in the AST after visiting children
    fn post_visit_exact_number_info(&mut self, _exact_number_info: &mut ExactNumberInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any except select item that appear in the AST before visiting children
    fn pre_visit_except_select_item(&mut self, _except_select_item: &mut ExceptSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any except select item that appear in the AST after visiting children
    fn post_visit_except_select_item(&mut self, _except_select_item: &mut ExceptSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exclude select item that appear in the AST before visiting children
    fn pre_visit_exclude_select_item(&mut self, _exclude_select_item: &mut ExcludeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any exclude select item that appear in the AST after visiting children
    fn post_visit_exclude_select_item(&mut self, _exclude_select_item: &mut ExcludeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expr with alias that appear in the AST before visiting children
    fn pre_visit_expr_with_alias(&mut self, _expr_with_alias: &mut ExprWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any expr with alias that appear in the AST after visiting children
    fn post_visit_expr_with_alias(&mut self, _expr_with_alias: &mut ExprWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any extract syntax that appear in the AST before visiting children
    fn pre_visit_extract_syntax(&mut self, _extract_syntax: &mut ExtractSyntax) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any extract syntax that appear in the AST after visiting children
    fn post_visit_extract_syntax(&mut self, _extract_syntax: &mut ExtractSyntax) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch that appear in the AST before visiting children
    fn pre_visit_fetch(&mut self, _fetch: &mut Fetch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch that appear in the AST after visiting children
    fn post_visit_fetch(&mut self, _fetch: &mut Fetch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch direction that appear in the AST before visiting children
    fn pre_visit_fetch_direction(&mut self, _fetch_direction: &mut FetchDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any fetch direction that appear in the AST after visiting children
    fn post_visit_fetch_direction(&mut self, _fetch_direction: &mut FetchDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file format that appear in the AST before visiting children
    fn pre_visit_file_format(&mut self, _file_format: &mut FileFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file format that appear in the AST after visiting children
    fn post_visit_file_format(&mut self, _file_format: &mut FileFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file staging command that appear in the AST before visiting children
    fn pre_visit_file_staging_command(&mut self, _file_staging_command: &mut FileStagingCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any file staging command that appear in the AST after visiting children
    fn post_visit_file_staging_command(&mut self, _file_staging_command: &mut FileStagingCommand) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush location that appear in the AST before visiting children
    fn pre_visit_flush_location(&mut self, _flush_location: &mut FlushLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush location that appear in the AST after visiting children
    fn post_visit_flush_location(&mut self, _flush_location: &mut FlushLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush type that appear in the AST before visiting children
    fn pre_visit_flush_type(&mut self, _flush_type: &mut FlushType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any flush type that appear in the AST after visiting children
    fn post_visit_flush_type(&mut self, _flush_type: &mut FlushType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for clause that appear in the AST before visiting children
    fn pre_visit_for_clause(&mut self, _for_clause: &mut ForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for clause that appear in the AST after visiting children
    fn post_visit_for_clause(&mut self, _for_clause: &mut ForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for xml that appear in the AST before visiting children
    fn pre_visit_for_xml(&mut self, _for_xml: &mut ForXml) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any for xml that appear in the AST after visiting children
    fn post_visit_for_xml(&mut self, _for_xml: &mut ForXml) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any format clause that appear in the AST before visiting children
    fn pre_visit_format_clause(&mut self, _format_clause: &mut FormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any format clause that appear in the AST after visiting children
    fn post_visit_format_clause(&mut self, _format_clause: &mut FormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any from table that appear in the AST before visiting children
    fn pre_visit_from_table(&mut self, _from_table: &mut FromTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any from table that appear in the AST after visiting children
    fn post_visit_from_table(&mut self, _from_table: &mut FromTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function that appear in the AST before visiting children
    fn pre_visit_function(&mut self, _function: &mut Function) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function that appear in the AST after visiting children
    fn post_visit_function(&mut self, _function: &mut Function) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg that appear in the AST before visiting children
    fn pre_visit_function_arg(&mut self, _function_arg: &mut FunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg that appear in the AST after visiting children
    fn post_visit_function_arg(&mut self, _function_arg: &mut FunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg expr that appear in the AST before visiting children
    fn pre_visit_function_arg_expr(&mut self, _function_arg_expr: &mut FunctionArgExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arg expr that appear in the AST after visiting children
    fn post_visit_function_arg_expr(&mut self, _function_arg_expr: &mut FunctionArgExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument clause that appear in the AST before visiting children
    fn pre_visit_function_argument_clause(&mut self, _function_argument_clause: &mut FunctionArgumentClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument clause that appear in the AST after visiting children
    fn post_visit_function_argument_clause(&mut self, _function_argument_clause: &mut FunctionArgumentClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument list that appear in the AST before visiting children
    fn pre_visit_function_argument_list(&mut self, _function_argument_list: &mut FunctionArgumentList) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function argument list that appear in the AST after visiting children
    fn post_visit_function_argument_list(&mut self, _function_argument_list: &mut FunctionArgumentList) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arguments that appear in the AST before visiting children
    fn pre_visit_function_arguments(&mut self, _function_arguments: &mut FunctionArguments) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function arguments that appear in the AST after visiting children
    fn post_visit_function_arguments(&mut self, _function_arguments: &mut FunctionArguments) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function behavior that appear in the AST before visiting children
    fn pre_visit_function_behavior(&mut self, _function_behavior: &mut FunctionBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function behavior that appear in the AST after visiting children
    fn post_visit_function_behavior(&mut self, _function_behavior: &mut FunctionBehavior) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function called on null that appear in the AST before visiting children
    fn pre_visit_function_called_on_null(&mut self, _function_called_on_null: &mut FunctionCalledOnNull) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function called on null that appear in the AST after visiting children
    fn post_visit_function_called_on_null(&mut self, _function_called_on_null: &mut FunctionCalledOnNull) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function desc that appear in the AST before visiting children
    fn pre_visit_function_desc(&mut self, _function_desc: &mut FunctionDesc) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function desc that appear in the AST after visiting children
    fn post_visit_function_desc(&mut self, _function_desc: &mut FunctionDesc) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function determinism specifier that appear in the AST before visiting children
    fn pre_visit_function_determinism_specifier(&mut self, _function_determinism_specifier: &mut FunctionDeterminismSpecifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function determinism specifier that appear in the AST after visiting children
    fn post_visit_function_determinism_specifier(&mut self, _function_determinism_specifier: &mut FunctionDeterminismSpecifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function parallel that appear in the AST before visiting children
    fn pre_visit_function_parallel(&mut self, _function_parallel: &mut FunctionParallel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any function parallel that appear in the AST after visiting children
    fn post_visit_function_parallel(&mut self, _function_parallel: &mut FunctionParallel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated as that appear in the AST before visiting children
    fn pre_visit_generated_as(&mut self, _generated_as: &mut GeneratedAs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated as that appear in the AST after visiting children
    fn post_visit_generated_as(&mut self, _generated_as: &mut GeneratedAs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated expression mode that appear in the AST before visiting children
    fn pre_visit_generated_expression_mode(&mut self, _generated_expression_mode: &mut GeneratedExpressionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any generated expression mode that appear in the AST after visiting children
    fn post_visit_generated_expression_mode(&mut self, _generated_expression_mode: &mut GeneratedExpressionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any geometric type kind that appear in the AST before visiting children
    fn pre_visit_geometric_type_kind(&mut self, _geometric_type_kind: &mut GeometricTypeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any geometric type kind that appear in the AST after visiting children
    fn post_visit_geometric_type_kind(&mut self, _geometric_type_kind: &mut GeometricTypeKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grant objects that appear in the AST before visiting children
    fn pre_visit_grant_objects(&mut self, _grant_objects: &mut GrantObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grant objects that appear in the AST after visiting children
    fn post_visit_grant_objects(&mut self, _grant_objects: &mut GrantObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee that appear in the AST before visiting children
    fn pre_visit_grantee(&mut self, _grantee: &mut Grantee) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee that appear in the AST after visiting children
    fn post_visit_grantee(&mut self, _grantee: &mut Grantee) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee name that appear in the AST before visiting children
    fn pre_visit_grantee_name(&mut self, _grantee_name: &mut GranteeName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantee name that appear in the AST after visiting children
    fn post_visit_grantee_name(&mut self, _grantee_name: &mut GranteeName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantees type that appear in the AST before visiting children
    fn pre_visit_grantees_type(&mut self, _grantees_type: &mut GranteesType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any grantees type that appear in the AST after visiting children
    fn post_visit_grantees_type(&mut self, _grantees_type: &mut GranteesType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by expr that appear in the AST before visiting children
    fn pre_visit_group_by_expr(&mut self, _group_by_expr: &mut GroupByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by expr that appear in the AST after visiting children
    fn post_visit_group_by_expr(&mut self, _group_by_expr: &mut GroupByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by with modifier that appear in the AST before visiting children
    fn pre_visit_group_by_with_modifier(&mut self, _group_by_with_modifier: &mut GroupByWithModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any group by with modifier that appear in the AST after visiting children
    fn post_visit_group_by_with_modifier(&mut self, _group_by_with_modifier: &mut GroupByWithModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound that appear in the AST before visiting children
    fn pre_visit_having_bound(&mut self, _having_bound: &mut HavingBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound that appear in the AST after visiting children
    fn post_visit_having_bound(&mut self, _having_bound: &mut HavingBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound kind that appear in the AST before visiting children
    fn pre_visit_having_bound_kind(&mut self, _having_bound_kind: &mut HavingBoundKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any having bound kind that appear in the AST after visiting children
    fn post_visit_having_bound_kind(&mut self, _having_bound_kind: &mut HavingBoundKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive delimiter that appear in the AST before visiting children
    fn pre_visit_hive_delimiter(&mut self, _hive_delimiter: &mut HiveDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive delimiter that appear in the AST after visiting children
    fn post_visit_hive_delimiter(&mut self, _hive_delimiter: &mut HiveDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive describe format that appear in the AST before visiting children
    fn pre_visit_hive_describe_format(&mut self, _hive_describe_format: &mut HiveDescribeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive describe format that appear in the AST after visiting children
    fn post_visit_hive_describe_format(&mut self, _hive_describe_format: &mut HiveDescribeFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive distribution style that appear in the AST before visiting children
    fn pre_visit_hive_distribution_style(&mut self, _hive_distribution_style: &mut HiveDistributionStyle) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive distribution style that appear in the AST after visiting children
    fn post_visit_hive_distribution_style(&mut self, _hive_distribution_style: &mut HiveDistributionStyle) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive format that appear in the AST before visiting children
    fn pre_visit_hive_format(&mut self, _hive_format: &mut HiveFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive format that appear in the AST after visiting children
    fn post_visit_hive_format(&mut self, _hive_format: &mut HiveFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive load data format that appear in the AST before visiting children
    fn pre_visit_hive_load_data_format(&mut self, _hive_load_data_format: &mut HiveLoadDataFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive load data format that appear in the AST after visiting children
    fn post_visit_hive_load_data_format(&mut self, _hive_load_data_format: &mut HiveLoadDataFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row delimiter that appear in the AST before visiting children
    fn pre_visit_hive_row_delimiter(&mut self, _hive_row_delimiter: &mut HiveRowDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row delimiter that appear in the AST after visiting children
    fn post_visit_hive_row_delimiter(&mut self, _hive_row_delimiter: &mut HiveRowDelimiter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row format that appear in the AST before visiting children
    fn pre_visit_hive_row_format(&mut self, _hive_row_format: &mut HiveRowFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive row format that appear in the AST after visiting children
    fn post_visit_hive_row_format(&mut self, _hive_row_format: &mut HiveRowFormat) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive set location that appear in the AST before visiting children
    fn pre_visit_hive_set_location(&mut self, _hive_set_location: &mut HiveSetLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any hive set location that appear in the AST after visiting children
    fn post_visit_hive_set_location(&mut self, _hive_set_location: &mut HiveSetLocation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident that appear in the AST before visiting children
    fn pre_visit_ident(&mut self, _ident: &mut Ident) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident that appear in the AST after visiting children
    fn post_visit_ident(&mut self, _ident: &mut Ident) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident with alias that appear in the AST before visiting children
    fn pre_visit_ident_with_alias(&mut self, _ident_with_alias: &mut IdentWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ident with alias that appear in the AST after visiting children
    fn post_visit_ident_with_alias(&mut self, _ident_with_alias: &mut IdentWithAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity parameters that appear in the AST before visiting children
    fn pre_visit_identity_parameters(&mut self, _identity_parameters: &mut IdentityParameters) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity parameters that appear in the AST after visiting children
    fn post_visit_identity_parameters(&mut self, _identity_parameters: &mut IdentityParameters) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property that appear in the AST before visiting children
    fn pre_visit_identity_property(&mut self, _identity_property: &mut IdentityProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property that appear in the AST after visiting children
    fn post_visit_identity_property(&mut self, _identity_property: &mut IdentityProperty) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property format kind that appear in the AST before visiting children
    fn pre_visit_identity_property_format_kind(&mut self, _identity_property_format_kind: &mut IdentityPropertyFormatKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property format kind that appear in the AST after visiting children
    fn post_visit_identity_property_format_kind(&mut self, _identity_property_format_kind: &mut IdentityPropertyFormatKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property kind that appear in the AST before visiting children
    fn pre_visit_identity_property_kind(&mut self, _identity_property_kind: &mut IdentityPropertyKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property kind that appear in the AST after visiting children
    fn post_visit_identity_property_kind(&mut self, _identity_property_kind: &mut IdentityPropertyKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property order that appear in the AST before visiting children
    fn pre_visit_identity_property_order(&mut self, _identity_property_order: &mut IdentityPropertyOrder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any identity property order that appear in the AST after visiting children
    fn post_visit_identity_property_order(&mut self, _identity_property_order: &mut IdentityPropertyOrder) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any if statement that appear in the AST before visiting children
    fn pre_visit_if_statement(&mut self, _if_statement: &mut IfStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any if statement that appear in the AST after visiting children
    fn post_visit_if_statement(&mut self, _if_statement: &mut IfStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ilike select item that appear in the AST before visiting children
    fn pre_visit_ilike_select_item(&mut self, _ilike_select_item: &mut IlikeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any ilike select item that appear in the AST after visiting children
    fn post_visit_ilike_select_item(&mut self, _ilike_select_item: &mut IlikeSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index column that appear in the AST before visiting children
    fn pre_visit_index_column(&mut self, _index_column: &mut IndexColumn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index column that appear in the AST after visiting children
    fn post_visit_index_column(&mut self, _index_column: &mut IndexColumn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index option that appear in the AST before visiting children
    fn pre_visit_index_option(&mut self, _index_option: &mut IndexOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index option that appear in the AST after visiting children
    fn post_visit_index_option(&mut self, _index_option: &mut IndexOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index type that appear in the AST before visiting children
    fn pre_visit_index_type(&mut self, _index_type: &mut IndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any index type that appear in the AST after visiting children
    fn post_visit_index_type(&mut self, _index_type: &mut IndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any input format clause that appear in the AST before visiting children
    fn pre_visit_input_format_clause(&mut self, _input_format_clause: &mut InputFormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any input format clause that appear in the AST after visiting children
    fn post_visit_input_format_clause(&mut self, _input_format_clause: &mut InputFormatClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert that appear in the AST before visiting children
    fn pre_visit_insert(&mut self, _insert: &mut Insert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert that appear in the AST after visiting children
    fn post_visit_insert(&mut self, _insert: &mut Insert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert aliases that appear in the AST before visiting children
    fn pre_visit_insert_aliases(&mut self, _insert_aliases: &mut InsertAliases) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any insert aliases that appear in the AST after visiting children
    fn post_visit_insert_aliases(&mut self, _insert_aliases: &mut InsertAliases) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate that appear in the AST before visiting children
    fn pre_visit_interpolate(&mut self, _interpolate: &mut Interpolate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate that appear in the AST after visiting children
    fn post_visit_interpolate(&mut self, _interpolate: &mut Interpolate) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate expr that appear in the AST before visiting children
    fn pre_visit_interpolate_expr(&mut self, _interpolate_expr: &mut InterpolateExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interpolate expr that appear in the AST after visiting children
    fn post_visit_interpolate_expr(&mut self, _interpolate_expr: &mut InterpolateExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interval that appear in the AST before visiting children
    fn pre_visit_interval(&mut self, _interval: &mut Interval) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any interval that appear in the AST after visiting children
    fn post_visit_interval(&mut self, _interval: &mut Interval) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join that appear in the AST before visiting children
    fn pre_visit_join(&mut self, _join: &mut Join) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join that appear in the AST after visiting children
    fn post_visit_join(&mut self, _join: &mut Join) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join constraint that appear in the AST before visiting children
    fn pre_visit_join_constraint(&mut self, _join_constraint: &mut JoinConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join constraint that appear in the AST after visiting children
    fn post_visit_join_constraint(&mut self, _join_constraint: &mut JoinConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join operator that appear in the AST before visiting children
    fn pre_visit_join_operator(&mut self, _join_operator: &mut JoinOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any join operator that appear in the AST after visiting children
    fn post_visit_join_operator(&mut self, _join_operator: &mut JoinOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json null clause that appear in the AST before visiting children
    fn pre_visit_json_null_clause(&mut self, _json_null_clause: &mut JsonNullClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json null clause that appear in the AST after visiting children
    fn post_visit_json_null_clause(&mut self, _json_null_clause: &mut JsonNullClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path that appear in the AST before visiting children
    fn pre_visit_json_path(&mut self, _json_path: &mut JsonPath) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path that appear in the AST after visiting children
    fn post_visit_json_path(&mut self, _json_path: &mut JsonPath) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path elem that appear in the AST before visiting children
    fn pre_visit_json_path_elem(&mut self, _json_path_elem: &mut JsonPathElem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any json path elem that appear in the AST after visiting children
    fn post_visit_json_path_elem(&mut self, _json_path_elem: &mut JsonPathElem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key or index display that appear in the AST before visiting children
    fn pre_visit_key_or_index_display(&mut self, _key_or_index_display: &mut KeyOrIndexDisplay) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key or index display that appear in the AST after visiting children
    fn post_visit_key_or_index_display(&mut self, _key_or_index_display: &mut KeyOrIndexDisplay) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option that appear in the AST before visiting children
    fn pre_visit_key_value_option(&mut self, _key_value_option: &mut KeyValueOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option that appear in the AST after visiting children
    fn post_visit_key_value_option(&mut self, _key_value_option: &mut KeyValueOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option type that appear in the AST before visiting children
    fn pre_visit_key_value_option_type(&mut self, _key_value_option_type: &mut KeyValueOptionType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value option type that appear in the AST after visiting children
    fn post_visit_key_value_option_type(&mut self, _key_value_option_type: &mut KeyValueOptionType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value options that appear in the AST before visiting children
    fn pre_visit_key_value_options(&mut self, _key_value_options: &mut KeyValueOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any key value options that appear in the AST after visiting children
    fn post_visit_key_value_options(&mut self, _key_value_options: &mut KeyValueOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any kill type that appear in the AST before visiting children
    fn pre_visit_kill_type(&mut self, _kill_type: &mut KillType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any kill type that appear in the AST after visiting children
    fn post_visit_kill_type(&mut self, _kill_type: &mut KillType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lambda function that appear in the AST before visiting children
    fn pre_visit_lambda_function(&mut self, _lambda_function: &mut LambdaFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lambda function that appear in the AST after visiting children
    fn post_visit_lambda_function(&mut self, _lambda_function: &mut LambdaFunction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lateral view that appear in the AST before visiting children
    fn pre_visit_lateral_view(&mut self, _lateral_view: &mut LateralView) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lateral view that appear in the AST after visiting children
    fn post_visit_lateral_view(&mut self, _lateral_view: &mut LateralView) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any limit clause that appear in the AST before visiting children
    fn pre_visit_limit_clause(&mut self, _limit_clause: &mut LimitClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any limit clause that appear in the AST after visiting children
    fn post_visit_limit_clause(&mut self, _limit_clause: &mut LimitClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any list agg on overflow that appear in the AST before visiting children
    fn pre_visit_list_agg_on_overflow(&mut self, _list_agg_on_overflow: &mut ListAggOnOverflow) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any list agg on overflow that appear in the AST after visiting children
    fn post_visit_list_agg_on_overflow(&mut self, _list_agg_on_overflow: &mut ListAggOnOverflow) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any location that appear in the AST before visiting children
    fn pre_visit_location(&mut self, _location: &mut Location) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any location that appear in the AST after visiting children
    fn post_visit_location(&mut self, _location: &mut Location) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock clause that appear in the AST before visiting children
    fn pre_visit_lock_clause(&mut self, _lock_clause: &mut LockClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock clause that appear in the AST after visiting children
    fn post_visit_lock_clause(&mut self, _lock_clause: &mut LockClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table that appear in the AST before visiting children
    fn pre_visit_lock_table(&mut self, _lock_table: &mut LockTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table that appear in the AST after visiting children
    fn post_visit_lock_table(&mut self, _lock_table: &mut LockTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table type that appear in the AST before visiting children
    fn pre_visit_lock_table_type(&mut self, _lock_table_type: &mut LockTableType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock table type that appear in the AST after visiting children
    fn post_visit_lock_table_type(&mut self, _lock_table_type: &mut LockTableType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock type that appear in the AST before visiting children
    fn pre_visit_lock_type(&mut self, _lock_type: &mut LockType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any lock type that appear in the AST after visiting children
    fn post_visit_lock_type(&mut self, _lock_type: &mut LockType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro arg that appear in the AST before visiting children
    fn pre_visit_macro_arg(&mut self, _macro_arg: &mut MacroArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro arg that appear in the AST after visiting children
    fn post_visit_macro_arg(&mut self, _macro_arg: &mut MacroArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro definition that appear in the AST before visiting children
    fn pre_visit_macro_definition(&mut self, _macro_definition: &mut MacroDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any macro definition that appear in the AST after visiting children
    fn post_visit_macro_definition(&mut self, _macro_definition: &mut MacroDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map that appear in the AST before visiting children
    fn pre_visit_map(&mut self, _map: &mut Map) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map that appear in the AST after visiting children
    fn post_visit_map(&mut self, _map: &mut Map) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map entry that appear in the AST before visiting children
    fn pre_visit_map_entry(&mut self, _map_entry: &mut MapEntry) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any map entry that appear in the AST after visiting children
    fn post_visit_map_entry(&mut self, _map_entry: &mut MapEntry) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize pattern that appear in the AST before visiting children
    fn pre_visit_match_recognize_pattern(&mut self, _match_recognize_pattern: &mut MatchRecognizePattern) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize pattern that appear in the AST after visiting children
    fn post_visit_match_recognize_pattern(&mut self, _match_recognize_pattern: &mut MatchRecognizePattern) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize symbol that appear in the AST before visiting children
    fn pre_visit_match_recognize_symbol(&mut self, _match_recognize_symbol: &mut MatchRecognizeSymbol) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any match recognize symbol that appear in the AST after visiting children
    fn post_visit_match_recognize_symbol(&mut self, _match_recognize_symbol: &mut MatchRecognizeSymbol) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any measure that appear in the AST before visiting children
    fn pre_visit_measure(&mut self, _measure: &mut Measure) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any measure that appear in the AST after visiting children
    fn post_visit_measure(&mut self, _measure: &mut Measure) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge action that appear in the AST before visiting children
    fn pre_visit_merge_action(&mut self, _merge_action: &mut MergeAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge action that appear in the AST after visiting children
    fn post_visit_merge_action(&mut self, _merge_action: &mut MergeAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause that appear in the AST before visiting children
    fn pre_visit_merge_clause(&mut self, _merge_clause: &mut MergeClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause that appear in the AST after visiting children
    fn post_visit_merge_clause(&mut self, _merge_clause: &mut MergeClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause kind that appear in the AST before visiting children
    fn pre_visit_merge_clause_kind(&mut self, _merge_clause_kind: &mut MergeClauseKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge clause kind that appear in the AST after visiting children
    fn post_visit_merge_clause_kind(&mut self, _merge_clause_kind: &mut MergeClauseKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert expr that appear in the AST before visiting children
    fn pre_visit_merge_insert_expr(&mut self, _merge_insert_expr: &mut MergeInsertExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert expr that appear in the AST after visiting children
    fn post_visit_merge_insert_expr(&mut self, _merge_insert_expr: &mut MergeInsertExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert kind that appear in the AST before visiting children
    fn pre_visit_merge_insert_kind(&mut self, _merge_insert_kind: &mut MergeInsertKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any merge insert kind that appear in the AST after visiting children
    fn post_visit_merge_insert_kind(&mut self, _merge_insert_kind: &mut MergeInsertKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any method that appear in the AST before visiting children
    fn pre_visit_method(&mut self, _method: &mut Method) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any method that appear in the AST after visiting children
    fn post_visit_method(&mut self, _method: &mut Method) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any min max value that appear in the AST before visiting children
    fn pre_visit_min_max_value(&mut self, _min_max_value: &mut MinMaxValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any min max value that appear in the AST after visiting children
    fn post_visit_min_max_value(&mut self, _min_max_value: &mut MinMaxValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any my sql column position that appear in the AST before visiting children
    fn pre_visit_my_sql_column_position(&mut self, _my_sql_column_position: &mut MySQLColumnPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any my sql column position that appear in the AST after visiting children
    fn post_visit_my_sql_column_position(&mut self, _my_sql_column_position: &mut MySQLColumnPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any mysql insert priority that appear in the AST before visiting children
    fn pre_visit_mysql_insert_priority(&mut self, _mysql_insert_priority: &mut MysqlInsertPriority) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any mysql insert priority that appear in the AST after visiting children
    fn post_visit_mysql_insert_priority(&mut self, _mysql_insert_priority: &mut MysqlInsertPriority) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window definition that appear in the AST before visiting children
    fn pre_visit_named_window_definition(&mut self, _named_window_definition: &mut NamedWindowDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window definition that appear in the AST after visiting children
    fn post_visit_named_window_definition(&mut self, _named_window_definition: &mut NamedWindowDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window expr that appear in the AST before visiting children
    fn pre_visit_named_window_expr(&mut self, _named_window_expr: &mut NamedWindowExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any named window expr that appear in the AST after visiting children
    fn post_visit_named_window_expr(&mut self, _named_window_expr: &mut NamedWindowExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any non block that appear in the AST before visiting children
    fn pre_visit_non_block(&mut self, _non_block: &mut NonBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any non block that appear in the AST after visiting children
    fn post_visit_non_block(&mut self, _non_block: &mut NonBlock) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any null treatment that appear in the AST before visiting children
    fn pre_visit_null_treatment(&mut self, _null_treatment: &mut NullTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any null treatment that appear in the AST after visiting children
    fn post_visit_null_treatment(&mut self, _null_treatment: &mut NullTreatment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any nulls distinct option that appear in the AST before visiting children
    fn pre_visit_nulls_distinct_option(&mut self, _nulls_distinct_option: &mut NullsDistinctOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any nulls distinct option that appear in the AST after visiting children
    fn post_visit_nulls_distinct_option(&mut self, _nulls_distinct_option: &mut NullsDistinctOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name that appear in the AST before visiting children
    fn pre_visit_object_name(&mut self, _object_name: &mut ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name that appear in the AST after visiting children
    fn post_visit_object_name(&mut self, _object_name: &mut ObjectName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name part that appear in the AST before visiting children
    fn pre_visit_object_name_part(&mut self, _object_name_part: &mut ObjectNamePart) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object name part that appear in the AST after visiting children
    fn post_visit_object_name_part(&mut self, _object_name_part: &mut ObjectNamePart) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object type that appear in the AST before visiting children
    fn pre_visit_object_type(&mut self, _object_type: &mut ObjectType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any object type that appear in the AST after visiting children
    fn post_visit_object_type(&mut self, _object_type: &mut ObjectType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset that appear in the AST before visiting children
    fn pre_visit_offset(&mut self, _offset: &mut Offset) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset that appear in the AST after visiting children
    fn post_visit_offset(&mut self, _offset: &mut Offset) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset rows that appear in the AST before visiting children
    fn pre_visit_offset_rows(&mut self, _offset_rows: &mut OffsetRows) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any offset rows that appear in the AST after visiting children
    fn post_visit_offset_rows(&mut self, _offset_rows: &mut OffsetRows) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on commit that appear in the AST before visiting children
    fn pre_visit_on_commit(&mut self, _on_commit: &mut OnCommit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on commit that appear in the AST after visiting children
    fn post_visit_on_commit(&mut self, _on_commit: &mut OnCommit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict that appear in the AST before visiting children
    fn pre_visit_on_conflict(&mut self, _on_conflict: &mut OnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict that appear in the AST after visiting children
    fn post_visit_on_conflict(&mut self, _on_conflict: &mut OnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict action that appear in the AST before visiting children
    fn pre_visit_on_conflict_action(&mut self, _on_conflict_action: &mut OnConflictAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any on conflict action that appear in the AST after visiting children
    fn post_visit_on_conflict_action(&mut self, _on_conflict_action: &mut OnConflictAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any one or many with parens that appear in the AST before visiting children
    fn pre_visit_one_or_many_with_parens<T: VisitMut>(&mut self, _one_or_many_with_parens: &mut OneOrManyWithParens<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any one or many with parens that appear in the AST after visiting children
    fn post_visit_one_or_many_with_parens<T: VisitMut>(&mut self, _one_or_many_with_parens: &mut OneOrManyWithParens<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any operate function arg that appear in the AST before visiting children
    fn pre_visit_operate_function_arg(&mut self, _operate_function_arg: &mut OperateFunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any operate function arg that appear in the AST after visiting children
    fn post_visit_operate_function_arg(&mut self, _operate_function_arg: &mut OperateFunctionArg) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by that appear in the AST before visiting children
    fn pre_visit_order_by(&mut self, _order_by: &mut OrderBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by that appear in the AST after visiting children
    fn post_visit_order_by(&mut self, _order_by: &mut OrderBy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by expr that appear in the AST before visiting children
    fn pre_visit_order_by_expr(&mut self, _order_by_expr: &mut OrderByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by expr that appear in the AST after visiting children
    fn post_visit_order_by_expr(&mut self, _order_by_expr: &mut OrderByExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by kind that appear in the AST before visiting children
    fn pre_visit_order_by_kind(&mut self, _order_by_kind: &mut OrderByKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by kind that appear in the AST after visiting children
    fn post_visit_order_by_kind(&mut self, _order_by_kind: &mut OrderByKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by options that appear in the AST before visiting children
    fn pre_visit_order_by_options(&mut self, _order_by_options: &mut OrderByOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any order by options that appear in the AST after visiting children
    fn post_visit_order_by_options(&mut self, _order_by_options: &mut OrderByOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any output clause that appear in the AST before visiting children
    fn pre_visit_output_clause(&mut self, _output_clause: &mut OutputClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any output clause that appear in the AST after visiting children
    fn post_visit_output_clause(&mut self, _output_clause: &mut OutputClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any owner that appear in the AST before visiting children
    fn pre_visit_owner(&mut self, _owner: &mut Owner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any owner that appear in the AST after visiting children
    fn post_visit_owner(&mut self, _owner: &mut Owner) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition that appear in the AST before visiting children
    fn pre_visit_partition(&mut self, _partition: &mut Partition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition that appear in the AST after visiting children
    fn post_visit_partition(&mut self, _partition: &mut Partition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition range direction that appear in the AST before visiting children
    fn pre_visit_partition_range_direction(&mut self, _partition_range_direction: &mut PartitionRangeDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any partition range direction that appear in the AST after visiting children
    fn post_visit_partition_range_direction(&mut self, _partition_range_direction: &mut PartitionRangeDirection) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any password that appear in the AST before visiting children
    fn pre_visit_password(&mut self, _password: &mut Password) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any password that appear in the AST after visiting children
    fn post_visit_password(&mut self, _password: &mut Password) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any pivot value source that appear in the AST before visiting children
    fn pre_visit_pivot_value_source(&mut self, _pivot_value_source: &mut PivotValueSource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any pivot value source that appear in the AST after visiting children
    fn post_visit_pivot_value_source(&mut self, _pivot_value_source: &mut PivotValueSource) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any privileges that appear in the AST before visiting children
    fn pre_visit_privileges(&mut self, _privileges: &mut Privileges) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any privileges that appear in the AST after visiting children
    fn post_visit_privileges(&mut self, _privileges: &mut Privileges) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any procedure param that appear in the AST before visiting children
    fn pre_visit_procedure_param(&mut self, _procedure_param: &mut ProcedureParam) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any procedure param that appear in the AST after visiting children
    fn post_visit_procedure_param(&mut self, _procedure_param: &mut ProcedureParam) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any projection select that appear in the AST before visiting children
    fn pre_visit_projection_select(&mut self, _projection_select: &mut ProjectionSelect) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any projection select that appear in the AST after visiting children
    fn post_visit_projection_select(&mut self, _projection_select: &mut ProjectionSelect) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rais error option that appear in the AST before visiting children
    fn pre_visit_rais_error_option(&mut self, _rais_error_option: &mut RaisErrorOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rais error option that appear in the AST after visiting children
    fn post_visit_rais_error_option(&mut self, _rais_error_option: &mut RaisErrorOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement that appear in the AST before visiting children
    fn pre_visit_raise_statement(&mut self, _raise_statement: &mut RaiseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement that appear in the AST after visiting children
    fn post_visit_raise_statement(&mut self, _raise_statement: &mut RaiseStatement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement value that appear in the AST before visiting children
    fn pre_visit_raise_statement_value(&mut self, _raise_statement_value: &mut RaiseStatementValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any raise statement value that appear in the AST after visiting children
    fn post_visit_raise_statement_value(&mut self, _raise_statement_value: &mut RaiseStatementValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any referential action that appear in the AST before visiting children
    fn pre_visit_referential_action(&mut self, _referential_action: &mut ReferentialAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any referential action that appear in the AST after visiting children
    fn post_visit_referential_action(&mut self, _referential_action: &mut ReferentialAction) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename select item that appear in the AST before visiting children
    fn pre_visit_rename_select_item(&mut self, _rename_select_item: &mut RenameSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename select item that appear in the AST after visiting children
    fn post_visit_rename_select_item(&mut self, _rename_select_item: &mut RenameSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename table that appear in the AST before visiting children
    fn pre_visit_rename_table(&mut self, _rename_table: &mut RenameTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rename table that appear in the AST after visiting children
    fn post_visit_rename_table(&mut self, _rename_table: &mut RenameTable) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any repetition quantifier that appear in the AST before visiting children
    fn pre_visit_repetition_quantifier(&mut self, _repetition_quantifier: &mut RepetitionQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any repetition quantifier that appear in the AST after visiting children
    fn post_visit_repetition_quantifier(&mut self, _repetition_quantifier: &mut RepetitionQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select element that appear in the AST before visiting children
    fn pre_visit_replace_select_element(&mut self, _replace_select_element: &mut ReplaceSelectElement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select element that appear in the AST after visiting children
    fn post_visit_replace_select_element(&mut self, _replace_select_element: &mut ReplaceSelectElement) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select item that appear in the AST before visiting children
    fn pre_visit_replace_select_item(&mut self, _replace_select_item: &mut ReplaceSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any replace select item that appear in the AST after visiting children
    fn post_visit_replace_select_item(&mut self, _replace_select_item: &mut ReplaceSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any reset config that appear in the AST before visiting children
    fn pre_visit_reset_config(&mut self, _reset_config: &mut ResetConfig) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any reset config that appear in the AST after visiting children
    fn post_visit_reset_config(&mut self, _reset_config: &mut ResetConfig) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any role option that appear in the AST before visiting children
    fn pre_visit_role_option(&mut self, _role_option: &mut RoleOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any role option that appear in the AST after visiting children
    fn post_visit_role_option(&mut self, _role_option: &mut RoleOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any row access policy that appear in the AST before visiting children
    fn pre_visit_row_access_policy(&mut self, _row_access_policy: &mut RowAccessPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any row access policy that appear in the AST after visiting children
    fn post_visit_row_access_policy(&mut self, _row_access_policy: &mut RowAccessPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rows per match that appear in the AST before visiting children
    fn pre_visit_rows_per_match(&mut self, _rows_per_match: &mut RowsPerMatch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any rows per match that appear in the AST after visiting children
    fn post_visit_rows_per_match(&mut self, _rows_per_match: &mut RowsPerMatch) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any schema name that appear in the AST before visiting children
    fn pre_visit_schema_name(&mut self, _schema_name: &mut SchemaName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any schema name that appear in the AST after visiting children
    fn post_visit_schema_name(&mut self, _schema_name: &mut SchemaName) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any search modifier that appear in the AST before visiting children
    fn pre_visit_search_modifier(&mut self, _search_modifier: &mut SearchModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any search modifier that appear in the AST after visiting children
    fn post_visit_search_modifier(&mut self, _search_modifier: &mut SearchModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secondary roles that appear in the AST before visiting children
    fn pre_visit_secondary_roles(&mut self, _secondary_roles: &mut SecondaryRoles) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secondary roles that appear in the AST after visiting children
    fn post_visit_secondary_roles(&mut self, _secondary_roles: &mut SecondaryRoles) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secret option that appear in the AST before visiting children
    fn pre_visit_secret_option(&mut self, _secret_option: &mut SecretOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any secret option that appear in the AST after visiting children
    fn post_visit_secret_option(&mut self, _secret_option: &mut SecretOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select that appear in the AST before visiting children
    fn pre_visit_select(&mut self, _select: &mut Select) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select that appear in the AST after visiting children
    fn post_visit_select(&mut self, _select: &mut Select) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select flavor that appear in the AST before visiting children
    fn pre_visit_select_flavor(&mut self, _select_flavor: &mut SelectFlavor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select flavor that appear in the AST after visiting children
    fn post_visit_select_flavor(&mut self, _select_flavor: &mut SelectFlavor) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select into that appear in the AST before visiting children
    fn pre_visit_select_into(&mut self, _select_into: &mut SelectInto) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select into that appear in the AST after visiting children
    fn post_visit_select_into(&mut self, _select_into: &mut SelectInto) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item that appear in the AST before visiting children
    fn pre_visit_select_item(&mut self, _select_item: &mut SelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item that appear in the AST after visiting children
    fn post_visit_select_item(&mut self, _select_item: &mut SelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item qualified wildcard kind that appear in the AST before visiting children
    fn pre_visit_select_item_qualified_wildcard_kind(&mut self, _select_item_qualified_wildcard_kind: &mut SelectItemQualifiedWildcardKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any select item qualified wildcard kind that appear in the AST after visiting children
    fn post_visit_select_item_qualified_wildcard_kind(&mut self, _select_item_qualified_wildcard_kind: &mut SelectItemQualifiedWildcardKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sequence options that appear in the AST before visiting children
    fn pre_visit_sequence_options(&mut self, _sequence_options: &mut SequenceOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sequence options that appear in the AST after visiting children
    fn post_visit_sequence_options(&mut self, _sequence_options: &mut SequenceOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param stats topic that appear in the AST before visiting children
    fn pre_visit_session_param_stats_topic(&mut self, _session_param_stats_topic: &mut SessionParamStatsTopic) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param stats topic that appear in the AST after visiting children
    fn post_visit_session_param_stats_topic(&mut self, _session_param_stats_topic: &mut SessionParamStatsTopic) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param value that appear in the AST before visiting children
    fn pre_visit_session_param_value(&mut self, _session_param_value: &mut SessionParamValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any session param value that appear in the AST after visiting children
    fn post_visit_session_param_value(&mut self, _session_param_value: &mut SessionParamValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set that appear in the AST before visiting children
    fn pre_visit_set(&mut self, _set: &mut Set) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set that appear in the AST after visiting children
    fn post_visit_set(&mut self, _set: &mut Set) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set assignment that appear in the AST before visiting children
    fn pre_visit_set_assignment(&mut self, _set_assignment: &mut SetAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set assignment that appear in the AST after visiting children
    fn post_visit_set_assignment(&mut self, _set_assignment: &mut SetAssignment) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set config value that appear in the AST before visiting children
    fn pre_visit_set_config_value(&mut self, _set_config_value: &mut SetConfigValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set config value that appear in the AST after visiting children
    fn post_visit_set_config_value(&mut self, _set_config_value: &mut SetConfigValue) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set expr that appear in the AST before visiting children
    fn pre_visit_set_expr(&mut self, _set_expr: &mut SetExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set expr that appear in the AST after visiting children
    fn post_visit_set_expr(&mut self, _set_expr: &mut SetExpr) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set operator that appear in the AST before visiting children
    fn pre_visit_set_operator(&mut self, _set_operator: &mut SetOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set operator that appear in the AST after visiting children
    fn post_visit_set_operator(&mut self, _set_operator: &mut SetOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set quantifier that appear in the AST before visiting children
    fn pre_visit_set_quantifier(&mut self, _set_quantifier: &mut SetQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set quantifier that appear in the AST after visiting children
    fn post_visit_set_quantifier(&mut self, _set_quantifier: &mut SetQuantifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table that appear in the AST before visiting children
    fn pre_visit_table(&mut self, _table: &mut Table) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table that appear in the AST after visiting children
    fn post_visit_table(&mut self, _table: &mut Table) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param generic that appear in the AST before visiting children
    fn pre_visit_set_session_param_generic(&mut self, _set_session_param_generic: &mut SetSessionParamGeneric) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param generic that appear in the AST after visiting children
    fn post_visit_set_session_param_generic(&mut self, _set_session_param_generic: &mut SetSessionParamGeneric) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param identity insert that appear in the AST before visiting children
    fn pre_visit_set_session_param_identity_insert(&mut self, _set_session_param_identity_insert: &mut SetSessionParamIdentityInsert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param identity insert that appear in the AST after visiting children
    fn post_visit_set_session_param_identity_insert(&mut self, _set_session_param_identity_insert: &mut SetSessionParamIdentityInsert) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param kind that appear in the AST before visiting children
    fn pre_visit_set_session_param_kind(&mut self, _set_session_param_kind: &mut SetSessionParamKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param kind that appear in the AST after visiting children
    fn post_visit_set_session_param_kind(&mut self, _set_session_param_kind: &mut SetSessionParamKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param offsets that appear in the AST before visiting children
    fn pre_visit_set_session_param_offsets(&mut self, _set_session_param_offsets: &mut SetSessionParamOffsets) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param offsets that appear in the AST after visiting children
    fn post_visit_set_session_param_offsets(&mut self, _set_session_param_offsets: &mut SetSessionParamOffsets) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param statistics that appear in the AST before visiting children
    fn pre_visit_set_session_param_statistics(&mut self, _set_session_param_statistics: &mut SetSessionParamStatistics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any set session param statistics that appear in the AST after visiting children
    fn post_visit_set_session_param_statistics(&mut self, _set_session_param_statistics: &mut SetSessionParamStatistics) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any setting that appear in the AST before visiting children
    fn pre_visit_setting(&mut self, _setting: &mut Setting) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any setting that appear in the AST after visiting children
    fn post_visit_setting(&mut self, _setting: &mut Setting) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show create object that appear in the AST before visiting children
    fn pre_visit_show_create_object(&mut self, _show_create_object: &mut ShowCreateObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show create object that appear in the AST after visiting children
    fn post_visit_show_create_object(&mut self, _show_create_object: &mut ShowCreateObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show objects that appear in the AST before visiting children
    fn pre_visit_show_objects(&mut self, _show_objects: &mut ShowObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show objects that appear in the AST after visiting children
    fn post_visit_show_objects(&mut self, _show_objects: &mut ShowObjects) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter that appear in the AST before visiting children
    fn pre_visit_show_statement_filter(&mut self, _show_statement_filter: &mut ShowStatementFilter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter that appear in the AST after visiting children
    fn post_visit_show_statement_filter(&mut self, _show_statement_filter: &mut ShowStatementFilter) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter position that appear in the AST before visiting children
    fn pre_visit_show_statement_filter_position(&mut self, _show_statement_filter_position: &mut ShowStatementFilterPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement filter position that appear in the AST after visiting children
    fn post_visit_show_statement_filter_position(&mut self, _show_statement_filter_position: &mut ShowStatementFilterPosition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in that appear in the AST before visiting children
    fn pre_visit_show_statement_in(&mut self, _show_statement_in: &mut ShowStatementIn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in that appear in the AST after visiting children
    fn post_visit_show_statement_in(&mut self, _show_statement_in: &mut ShowStatementIn) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in clause that appear in the AST before visiting children
    fn pre_visit_show_statement_in_clause(&mut self, _show_statement_in_clause: &mut ShowStatementInClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in clause that appear in the AST after visiting children
    fn post_visit_show_statement_in_clause(&mut self, _show_statement_in_clause: &mut ShowStatementInClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in parent type that appear in the AST before visiting children
    fn pre_visit_show_statement_in_parent_type(&mut self, _show_statement_in_parent_type: &mut ShowStatementInParentType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement in parent type that appear in the AST after visiting children
    fn post_visit_show_statement_in_parent_type(&mut self, _show_statement_in_parent_type: &mut ShowStatementInParentType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement options that appear in the AST before visiting children
    fn pre_visit_show_statement_options(&mut self, _show_statement_options: &mut ShowStatementOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any show statement options that appear in the AST after visiting children
    fn post_visit_show_statement_options(&mut self, _show_statement_options: &mut ShowStatementOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any span that appear in the AST before visiting children
    fn pre_visit_span(&mut self, _span: &mut Span) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any span that appear in the AST after visiting children
    fn post_visit_span(&mut self, _span: &mut Span) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sql option that appear in the AST before visiting children
    fn pre_visit_sql_option(&mut self, _sql_option: &mut SqlOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sql option that appear in the AST after visiting children
    fn post_visit_sql_option(&mut self, _sql_option: &mut SqlOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sqlite on conflict that appear in the AST before visiting children
    fn pre_visit_sqlite_on_conflict(&mut self, _sqlite_on_conflict: &mut SqliteOnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any sqlite on conflict that appear in the AST after visiting children
    fn post_visit_sqlite_on_conflict(&mut self, _sqlite_on_conflict: &mut SqliteOnConflict) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage load select item that appear in the AST before visiting children
    fn pre_visit_stage_load_select_item(&mut self, _stage_load_select_item: &mut StageLoadSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage load select item that appear in the AST after visiting children
    fn post_visit_stage_load_select_item(&mut self, _stage_load_select_item: &mut StageLoadSelectItem) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage params object that appear in the AST before visiting children
    fn pre_visit_stage_params_object(&mut self, _stage_params_object: &mut StageParamsObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any stage params object that appear in the AST after visiting children
    fn post_visit_stage_params_object(&mut self, _stage_params_object: &mut StageParamsObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any storage serialization policy that appear in the AST before visiting children
    fn pre_visit_storage_serialization_policy(&mut self, _storage_serialization_policy: &mut StorageSerializationPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any storage serialization policy that appear in the AST after visiting children
    fn post_visit_storage_serialization_policy(&mut self, _storage_serialization_policy: &mut StorageSerializationPolicy) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct bracket kind that appear in the AST before visiting children
    fn pre_visit_struct_bracket_kind(&mut self, _struct_bracket_kind: &mut StructBracketKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct bracket kind that appear in the AST after visiting children
    fn post_visit_struct_bracket_kind(&mut self, _struct_bracket_kind: &mut StructBracketKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct field that appear in the AST before visiting children
    fn pre_visit_struct_field(&mut self, _struct_field: &mut StructField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any struct field that appear in the AST after visiting children
    fn post_visit_struct_field(&mut self, _struct_field: &mut StructField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any subscript that appear in the AST before visiting children
    fn pre_visit_subscript(&mut self, _subscript: &mut Subscript) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any subscript that appear in the AST after visiting children
    fn post_visit_subscript(&mut self, _subscript: &mut Subscript) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any symbol definition that appear in the AST before visiting children
    fn pre_visit_symbol_definition(&mut self, _symbol_definition: &mut SymbolDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any symbol definition that appear in the AST after visiting children
    fn post_visit_symbol_definition(&mut self, _symbol_definition: &mut SymbolDefinition) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias that appear in the AST before visiting children
    fn pre_visit_table_alias(&mut self, _table_alias: &mut TableAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias that appear in the AST after visiting children
    fn post_visit_table_alias(&mut self, _table_alias: &mut TableAlias) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias column def that appear in the AST before visiting children
    fn pre_visit_table_alias_column_def(&mut self, _table_alias_column_def: &mut TableAliasColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table alias column def that appear in the AST after visiting children
    fn post_visit_table_alias_column_def(&mut self, _table_alias_column_def: &mut TableAliasColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table constraint that appear in the AST before visiting children
    fn pre_visit_table_constraint(&mut self, _table_constraint: &mut TableConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table constraint that appear in the AST after visiting children
    fn post_visit_table_constraint(&mut self, _table_constraint: &mut TableConstraint) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table engine that appear in the AST before visiting children
    fn pre_visit_table_engine(&mut self, _table_engine: &mut TableEngine) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table engine that appear in the AST after visiting children
    fn post_visit_table_engine(&mut self, _table_engine: &mut TableEngine) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table function args that appear in the AST before visiting children
    fn pre_visit_table_function_args(&mut self, _table_function_args: &mut TableFunctionArgs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table function args that appear in the AST after visiting children
    fn post_visit_table_function_args(&mut self, _table_function_args: &mut TableFunctionArgs) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint for clause that appear in the AST before visiting children
    fn pre_visit_table_index_hint_for_clause(&mut self, _table_index_hint_for_clause: &mut TableIndexHintForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint for clause that appear in the AST after visiting children
    fn post_visit_table_index_hint_for_clause(&mut self, _table_index_hint_for_clause: &mut TableIndexHintForClause) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint type that appear in the AST before visiting children
    fn pre_visit_table_index_hint_type(&mut self, _table_index_hint_type: &mut TableIndexHintType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hint type that appear in the AST after visiting children
    fn post_visit_table_index_hint_type(&mut self, _table_index_hint_type: &mut TableIndexHintType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hints that appear in the AST before visiting children
    fn pre_visit_table_index_hints(&mut self, _table_index_hints: &mut TableIndexHints) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index hints that appear in the AST after visiting children
    fn post_visit_table_index_hints(&mut self, _table_index_hints: &mut TableIndexHints) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index type that appear in the AST before visiting children
    fn pre_visit_table_index_type(&mut self, _table_index_type: &mut TableIndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table index type that appear in the AST after visiting children
    fn post_visit_table_index_type(&mut self, _table_index_type: &mut TableIndexType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table object that appear in the AST before visiting children
    fn pre_visit_table_object(&mut self, _table_object: &mut TableObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table object that appear in the AST after visiting children
    fn post_visit_table_object(&mut self, _table_object: &mut TableObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table options clustered that appear in the AST before visiting children
    fn pre_visit_table_options_clustered(&mut self, _table_options_clustered: &mut TableOptionsClustered) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table options clustered that appear in the AST after visiting children
    fn post_visit_table_options_clustered(&mut self, _table_options_clustered: &mut TableOptionsClustered) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample that appear in the AST before visiting children
    fn pre_visit_table_sample(&mut self, _table_sample: &mut TableSample) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample that appear in the AST after visiting children
    fn post_visit_table_sample(&mut self, _table_sample: &mut TableSample) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample bucket that appear in the AST before visiting children
    fn pre_visit_table_sample_bucket(&mut self, _table_sample_bucket: &mut TableSampleBucket) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample bucket that appear in the AST after visiting children
    fn post_visit_table_sample_bucket(&mut self, _table_sample_bucket: &mut TableSampleBucket) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample method that appear in the AST before visiting children
    fn pre_visit_table_sample_method(&mut self, _table_sample_method: &mut TableSampleMethod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample method that appear in the AST after visiting children
    fn post_visit_table_sample_method(&mut self, _table_sample_method: &mut TableSampleMethod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample modifier that appear in the AST before visiting children
    fn pre_visit_table_sample_modifier(&mut self, _table_sample_modifier: &mut TableSampleModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample modifier that appear in the AST after visiting children
    fn post_visit_table_sample_modifier(&mut self, _table_sample_modifier: &mut TableSampleModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample quantity that appear in the AST before visiting children
    fn pre_visit_table_sample_quantity(&mut self, _table_sample_quantity: &mut TableSampleQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample quantity that appear in the AST after visiting children
    fn post_visit_table_sample_quantity(&mut self, _table_sample_quantity: &mut TableSampleQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed that appear in the AST before visiting children
    fn pre_visit_table_sample_seed(&mut self, _table_sample_seed: &mut TableSampleSeed) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed that appear in the AST after visiting children
    fn post_visit_table_sample_seed(&mut self, _table_sample_seed: &mut TableSampleSeed) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed modifier that appear in the AST before visiting children
    fn pre_visit_table_sample_seed_modifier(&mut self, _table_sample_seed_modifier: &mut TableSampleSeedModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample seed modifier that appear in the AST after visiting children
    fn post_visit_table_sample_seed_modifier(&mut self, _table_sample_seed_modifier: &mut TableSampleSeedModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample unit that appear in the AST before visiting children
    fn pre_visit_table_sample_unit(&mut self, _table_sample_unit: &mut TableSampleUnit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table sample unit that appear in the AST after visiting children
    fn post_visit_table_sample_unit(&mut self, _table_sample_unit: &mut TableSampleUnit) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table version that appear in the AST before visiting children
    fn pre_visit_table_version(&mut self, _table_version: &mut TableVersion) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table version that appear in the AST after visiting children
    fn post_visit_table_version(&mut self, _table_version: &mut TableVersion) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table with joins that appear in the AST before visiting children
    fn pre_visit_table_with_joins(&mut self, _table_with_joins: &mut TableWithJoins) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any table with joins that appear in the AST after visiting children
    fn post_visit_table_with_joins(&mut self, _table_with_joins: &mut TableWithJoins) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tag that appear in the AST before visiting children
    fn pre_visit_tag(&mut self, _tag: &mut Tag) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tag that appear in the AST after visiting children
    fn post_visit_tag(&mut self, _tag: &mut Tag) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tags column option that appear in the AST before visiting children
    fn pre_visit_tags_column_option(&mut self, _tags_column_option: &mut TagsColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any tags column option that appear in the AST after visiting children
    fn post_visit_tags_column_option(&mut self, _tags_column_option: &mut TagsColumnOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any timezone info that appear in the AST before visiting children
    fn pre_visit_timezone_info(&mut self, _timezone_info: &mut TimezoneInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any timezone info that appear in the AST after visiting children
    fn post_visit_timezone_info(&mut self, _timezone_info: &mut TimezoneInfo) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token that appear in the AST before visiting children
    fn pre_visit_token(&mut self, _token: &mut Token) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token that appear in the AST after visiting children
    fn post_visit_token(&mut self, _token: &mut Token) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token with span that appear in the AST before visiting children
    fn pre_visit_token_with_span(&mut self, _token_with_span: &mut TokenWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any token with span that appear in the AST after visiting children
    fn post_visit_token_with_span(&mut self, _token_with_span: &mut TokenWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top that appear in the AST before visiting children
    fn pre_visit_top(&mut self, _top: &mut Top) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top that appear in the AST after visiting children
    fn post_visit_top(&mut self, _top: &mut Top) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top quantity that appear in the AST before visiting children
    fn pre_visit_top_quantity(&mut self, _top_quantity: &mut TopQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any top quantity that appear in the AST after visiting children
    fn post_visit_top_quantity(&mut self, _top_quantity: &mut TopQuantity) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction access mode that appear in the AST before visiting children
    fn pre_visit_transaction_access_mode(&mut self, _transaction_access_mode: &mut TransactionAccessMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction access mode that appear in the AST after visiting children
    fn post_visit_transaction_access_mode(&mut self, _transaction_access_mode: &mut TransactionAccessMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction isolation level that appear in the AST before visiting children
    fn pre_visit_transaction_isolation_level(&mut self, _transaction_isolation_level: &mut TransactionIsolationLevel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction isolation level that appear in the AST after visiting children
    fn post_visit_transaction_isolation_level(&mut self, _transaction_isolation_level: &mut TransactionIsolationLevel) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction mode that appear in the AST before visiting children
    fn pre_visit_transaction_mode(&mut self, _transaction_mode: &mut TransactionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction mode that appear in the AST after visiting children
    fn post_visit_transaction_mode(&mut self, _transaction_mode: &mut TransactionMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction modifier that appear in the AST before visiting children
    fn pre_visit_transaction_modifier(&mut self, _transaction_modifier: &mut TransactionModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any transaction modifier that appear in the AST after visiting children
    fn post_visit_transaction_modifier(&mut self, _transaction_modifier: &mut TransactionModifier) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger event that appear in the AST before visiting children
    fn pre_visit_trigger_event(&mut self, _trigger_event: &mut TriggerEvent) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger event that appear in the AST after visiting children
    fn post_visit_trigger_event(&mut self, _trigger_event: &mut TriggerEvent) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body that appear in the AST before visiting children
    fn pre_visit_trigger_exec_body(&mut self, _trigger_exec_body: &mut TriggerExecBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body that appear in the AST after visiting children
    fn post_visit_trigger_exec_body(&mut self, _trigger_exec_body: &mut TriggerExecBody) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body type that appear in the AST before visiting children
    fn pre_visit_trigger_exec_body_type(&mut self, _trigger_exec_body_type: &mut TriggerExecBodyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger exec body type that appear in the AST after visiting children
    fn post_visit_trigger_exec_body_type(&mut self, _trigger_exec_body_type: &mut TriggerExecBodyType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger object that appear in the AST before visiting children
    fn pre_visit_trigger_object(&mut self, _trigger_object: &mut TriggerObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger object that appear in the AST after visiting children
    fn post_visit_trigger_object(&mut self, _trigger_object: &mut TriggerObject) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger period that appear in the AST before visiting children
    fn pre_visit_trigger_period(&mut self, _trigger_period: &mut TriggerPeriod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger period that appear in the AST after visiting children
    fn post_visit_trigger_period(&mut self, _trigger_period: &mut TriggerPeriod) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing that appear in the AST before visiting children
    fn pre_visit_trigger_referencing(&mut self, _trigger_referencing: &mut TriggerReferencing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing that appear in the AST after visiting children
    fn post_visit_trigger_referencing(&mut self, _trigger_referencing: &mut TriggerReferencing) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing type that appear in the AST before visiting children
    fn pre_visit_trigger_referencing_type(&mut self, _trigger_referencing_type: &mut TriggerReferencingType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trigger referencing type that appear in the AST after visiting children
    fn post_visit_trigger_referencing_type(&mut self, _trigger_referencing_type: &mut TriggerReferencingType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trim where field that appear in the AST before visiting children
    fn pre_visit_trim_where_field(&mut self, _trim_where_field: &mut TrimWhereField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any trim where field that appear in the AST after visiting children
    fn post_visit_trim_where_field(&mut self, _trim_where_field: &mut TrimWhereField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any truncate identity option that appear in the AST before visiting children
    fn pre_visit_truncate_identity_option(&mut self, _truncate_identity_option: &mut TruncateIdentityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any truncate identity option that appear in the AST after visiting children
    fn post_visit_truncate_identity_option(&mut self, _truncate_identity_option: &mut TruncateIdentityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any unary operator that appear in the AST before visiting children
    fn pre_visit_unary_operator(&mut self, _unary_operator: &mut UnaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any unary operator that appear in the AST after visiting children
    fn post_visit_unary_operator(&mut self, _unary_operator: &mut UnaryOperator) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any union field that appear in the AST before visiting children
    fn pre_visit_union_field(&mut self, _union_field: &mut UnionField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any union field that appear in the AST after visiting children
    fn post_visit_union_field(&mut self, _union_field: &mut UnionField) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any update table from kind that appear in the AST before visiting children
    fn pre_visit_update_table_from_kind(&mut self, _update_table_from_kind: &mut UpdateTableFromKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any update table from kind that appear in the AST after visiting children
    fn post_visit_update_table_from_kind(&mut self, _update_table_from_kind: &mut UpdateTableFromKind) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any use that appear in the AST before visiting children
    fn pre_visit_use(&mut self, _use: &mut Use) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any use that appear in the AST after visiting children
    fn post_visit_use(&mut self, _use: &mut Use) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type composite attribute def that appear in the AST before visiting children
    fn pre_visit_user_defined_type_composite_attribute_def(&mut self, _user_defined_type_composite_attribute_def: &mut UserDefinedTypeCompositeAttributeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type composite attribute def that appear in the AST after visiting children
    fn post_visit_user_defined_type_composite_attribute_def(&mut self, _user_defined_type_composite_attribute_def: &mut UserDefinedTypeCompositeAttributeDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type representation that appear in the AST before visiting children
    fn pre_visit_user_defined_type_representation(&mut self, _user_defined_type_representation: &mut UserDefinedTypeRepresentation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any user defined type representation that appear in the AST after visiting children
    fn post_visit_user_defined_type_representation(&mut self, _user_defined_type_representation: &mut UserDefinedTypeRepresentation) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any utility option that appear in the AST before visiting children
    fn pre_visit_utility_option(&mut self, _utility_option: &mut UtilityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any utility option that appear in the AST after visiting children
    fn post_visit_utility_option(&mut self, _utility_option: &mut UtilityOption) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value table mode that appear in the AST before visiting children
    fn pre_visit_value_table_mode(&mut self, _value_table_mode: &mut ValueTableMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value table mode that appear in the AST after visiting children
    fn post_visit_value_table_mode(&mut self, _value_table_mode: &mut ValueTableMode) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value with span that appear in the AST before visiting children
    fn pre_visit_value_with_span(&mut self, _value_with_span: &mut ValueWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any value with span that appear in the AST after visiting children
    fn post_visit_value_with_span(&mut self, _value_with_span: &mut ValueWithSpan) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any values that appear in the AST before visiting children
    fn pre_visit_values(&mut self, _values: &mut Values) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any values that appear in the AST after visiting children
    fn post_visit_values(&mut self, _values: &mut Values) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any view column def that appear in the AST before visiting children
    fn pre_visit_view_column_def(&mut self, _view_column_def: &mut ViewColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any view column def that appear in the AST after visiting children
    fn post_visit_view_column_def(&mut self, _view_column_def: &mut ViewColumnDef) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any whitespace that appear in the AST before visiting children
    fn pre_visit_whitespace(&mut self, _whitespace: &mut Whitespace) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any whitespace that appear in the AST after visiting children
    fn post_visit_whitespace(&mut self, _whitespace: &mut Whitespace) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wildcard additional options that appear in the AST before visiting children
    fn pre_visit_wildcard_additional_options(&mut self, _wildcard_additional_options: &mut WildcardAdditionalOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wildcard additional options that appear in the AST after visiting children
    fn post_visit_wildcard_additional_options(&mut self, _wildcard_additional_options: &mut WildcardAdditionalOptions) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame that appear in the AST before visiting children
    fn pre_visit_window_frame(&mut self, _window_frame: &mut WindowFrame) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame that appear in the AST after visiting children
    fn post_visit_window_frame(&mut self, _window_frame: &mut WindowFrame) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame bound that appear in the AST before visiting children
    fn pre_visit_window_frame_bound(&mut self, _window_frame_bound: &mut WindowFrameBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame bound that appear in the AST after visiting children
    fn post_visit_window_frame_bound(&mut self, _window_frame_bound: &mut WindowFrameBound) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame units that appear in the AST before visiting children
    fn pre_visit_window_frame_units(&mut self, _window_frame_units: &mut WindowFrameUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window frame units that appear in the AST after visiting children
    fn post_visit_window_frame_units(&mut self, _window_frame_units: &mut WindowFrameUnits) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window spec that appear in the AST before visiting children
    fn pre_visit_window_spec(&mut self, _window_spec: &mut WindowSpec) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window spec that appear in the AST after visiting children
    fn post_visit_window_spec(&mut self, _window_spec: &mut WindowSpec) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window type that appear in the AST before visiting children
    fn pre_visit_window_type(&mut self, _window_type: &mut WindowType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any window type that appear in the AST after visiting children
    fn post_visit_window_type(&mut self, _window_type: &mut WindowType) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with that appear in the AST before visiting children
    fn pre_visit_with(&mut self, _with: &mut With) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with that appear in the AST after visiting children
    fn post_visit_with(&mut self, _with: &mut With) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with fill that appear in the AST before visiting children
    fn pre_visit_with_fill(&mut self, _with_fill: &mut WithFill) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any with fill that appear in the AST after visiting children
    fn post_visit_with_fill(&mut self, _with_fill: &mut WithFill) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any word that appear in the AST before visiting children
    fn pre_visit_word(&mut self, _word: &mut Word) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any word that appear in the AST after visiting children
    fn post_visit_word(&mut self, _word: &mut Word) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wrapped collection that appear in the AST before visiting children
    fn pre_visit_wrapped_collection<T: VisitMut>(&mut self, _wrapped_collection: &mut WrappedCollection<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    /// Invoked for any wrapped collection that appear in the AST after visiting children
    fn post_visit_wrapped_collection<T: VisitMut>(&mut self, _wrapped_collection: &mut WrappedCollection<T>) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }
}

struct RelationVisitor<F>(F);

impl<E, F: FnMut(&ObjectName) -> ControlFlow<E>> Visitor for RelationVisitor<F> {
    type Break = E;

    fn pre_visit_relation(&mut self, relation: &ObjectName) -> ControlFlow<Self::Break> {
        self.0(relation)
    }
}

impl<E, F: FnMut(&mut ObjectName) -> ControlFlow<E>> VisitorMut for RelationVisitor<F> {
    type Break = E;

    fn post_visit_relation(&mut self, relation: &mut ObjectName) -> ControlFlow<Self::Break> {
        self.0(relation)
    }
}

/// Invokes the provided closure on all relations (e.g. table names) present in `v`
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{visit_relations};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT a FROM foo where x IN (SELECT y FROM bar)";
/// let statements = Parser::parse_sql(&GenericDialect{}, sql)
///    .unwrap();
///
/// // visit statements, capturing relations (table names)
/// let mut visited = vec![];
/// visit_relations(&statements, |relation| {
///   visited.push(format!("RELATION: {}", relation));
///   ControlFlow::<()>::Continue(())
/// });
///
/// let expected : Vec<_> = [
///   "RELATION: foo",
///   "RELATION: bar",
/// ]
///   .into_iter().map(|s| s.to_string()).collect();
///
/// assert_eq!(visited, expected);
/// ```
pub fn visit_relations<V, E, F>(v: &V, f: F) -> ControlFlow<E>
where
    V: Visit,
    F: FnMut(&ObjectName) -> ControlFlow<E>,
{
    let mut visitor = RelationVisitor(f);
    v.visit(&mut visitor)?;
    ControlFlow::Continue(())
}

/// Invokes the provided closure with a mutable reference to all relations (e.g. table names)
/// present in `v`.
///
/// When the closure mutates its argument, the new mutated relation will not be visited again.
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{ObjectName, ObjectNamePart, Ident, visit_relations_mut};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT a FROM foo";
/// let mut statements = Parser::parse_sql(&GenericDialect{}, sql)
///    .unwrap();
///
/// // visit statements, renaming table foo to bar
/// visit_relations_mut(&mut statements, |table| {
///   table.0[0] = ObjectNamePart::Identifier(Ident::new("bar"));
///   ControlFlow::<()>::Continue(())
/// });
///
/// assert_eq!(statements[0].to_string(), "SELECT a FROM bar");
/// ```
pub fn visit_relations_mut<V, E, F>(v: &mut V, f: F) -> ControlFlow<E>
where
    V: VisitMut,
    F: FnMut(&mut ObjectName) -> ControlFlow<E>,
{
    let mut visitor = RelationVisitor(f);
    v.visit(&mut visitor)?;
    ControlFlow::Continue(())
}

struct ExprVisitor<F>(F);

impl<E, F: FnMut(&Expr) -> ControlFlow<E>> Visitor for ExprVisitor<F> {
    type Break = E;

    fn pre_visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::Break> {
        self.0(expr)
    }
}

impl<E, F: FnMut(&mut Expr) -> ControlFlow<E>> VisitorMut for ExprVisitor<F> {
    type Break = E;

    fn post_visit_expr(&mut self, expr: &mut Expr) -> ControlFlow<Self::Break> {
        self.0(expr)
    }
}

/// Invokes the provided closure on all expressions (e.g. `1 + 2`) present in `v`
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{visit_expressions};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT a FROM foo where x IN (SELECT y FROM bar)";
/// let statements = Parser::parse_sql(&GenericDialect{}, sql)
///    .unwrap();
///
/// // visit all expressions
/// let mut visited = vec![];
/// visit_expressions(&statements, |expr| {
///   visited.push(format!("EXPR: {}", expr));
///   ControlFlow::<()>::Continue(())
/// });
///
/// let expected : Vec<_> = [
///   "EXPR: a",
///   "EXPR: x IN (SELECT y FROM bar)",
///   "EXPR: x",
///   "EXPR: y",
/// ]
///   .into_iter().map(|s| s.to_string()).collect();
///
/// assert_eq!(visited, expected);
/// ```
pub fn visit_expressions<V, E, F>(v: &V, f: F) -> ControlFlow<E>
where
    V: Visit,
    F: FnMut(&Expr) -> ControlFlow<E>,
{
    let mut visitor = ExprVisitor(f);
    v.visit(&mut visitor)?;
    ControlFlow::Continue(())
}

/// Invokes the provided closure iteratively with a mutable reference to all expressions
/// present in `v`.
///
/// This performs a depth-first search, so if the closure mutates the expression
///
/// # Example
///
/// ## Remove all select limits in sub-queries
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{Expr, visit_expressions_mut, visit_statements_mut};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT (SELECT y FROM z LIMIT 9) FROM t LIMIT 3";
/// let mut statements = Parser::parse_sql(&GenericDialect{}, sql).unwrap();
///
/// // Remove all select limits in sub-queries
/// visit_expressions_mut(&mut statements, |expr| {
///   if let Expr::Subquery(q) = expr {
///      q.limit_clause = None;
///   }
///   ControlFlow::<()>::Continue(())
/// });
///
/// assert_eq!(statements[0].to_string(), "SELECT (SELECT y FROM z) FROM t LIMIT 3");
/// ```
///
/// ## Wrap column name in function call
///
/// This demonstrates how to effectively replace an expression with another more complicated one
/// that references the original. This example avoids unnecessary allocations by using the
/// [`std::mem`] family of functions.
///
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::*;
/// # use core::ops::ControlFlow;
/// let sql = "SELECT x, y FROM t";
/// let mut statements = Parser::parse_sql(&GenericDialect{}, sql).unwrap();
///
/// visit_expressions_mut(&mut statements, |expr| {
///   if matches!(expr, Expr::Identifier(col_name) if col_name.value == "x") {
///     let old_expr = std::mem::replace(expr, Expr::value(Value::Null));
///     *expr = Expr::Function(Function {
///           name: ObjectName::from(vec![Ident::new("f")]),
///           uses_odbc_syntax: false,
///           args: FunctionArguments::List(FunctionArgumentList {
///               duplicate_treatment: None,
///               args: vec![FunctionArg::Unnamed(FunctionArgExpr::Expr(old_expr))],
///               clauses: vec![],
///           }),
///           null_treatment: None,
///           filter: None,
///           over: None,
///           parameters: FunctionArguments::None,
///           within_group: vec![],
///      });
///   }
///   ControlFlow::<()>::Continue(())
/// });
///
/// assert_eq!(statements[0].to_string(), "SELECT f(x), y FROM t");
/// ```
pub fn visit_expressions_mut<V, E, F>(v: &mut V, f: F) -> ControlFlow<E>
where
    V: VisitMut,
    F: FnMut(&mut Expr) -> ControlFlow<E>,
{
    v.visit(&mut ExprVisitor(f))?;
    ControlFlow::Continue(())
}

struct StatementVisitor<F>(F);

impl<E, F: FnMut(&Statement) -> ControlFlow<E>> Visitor for StatementVisitor<F> {
    type Break = E;

    fn pre_visit_statement(&mut self, statement: &Statement) -> ControlFlow<Self::Break> {
        self.0(statement)
    }
}

impl<E, F: FnMut(&mut Statement) -> ControlFlow<E>> VisitorMut for StatementVisitor<F> {
    type Break = E;

    fn post_visit_statement(&mut self, statement: &mut Statement) -> ControlFlow<Self::Break> {
        self.0(statement)
    }
}

/// Invokes the provided closure iteratively with a mutable reference to all statements
/// present in `v` (e.g. `SELECT`, `CREATE TABLE`, etc).
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{visit_statements};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT a FROM foo where x IN (SELECT y FROM bar); CREATE TABLE baz(q int)";
/// let statements = Parser::parse_sql(&GenericDialect{}, sql)
///    .unwrap();
///
/// // visit all statements
/// let mut visited = vec![];
/// visit_statements(&statements, |stmt| {
///   visited.push(format!("STATEMENT: {}", stmt));
///   ControlFlow::<()>::Continue(())
/// });
///
/// let expected : Vec<_> = [
///   "STATEMENT: SELECT a FROM foo WHERE x IN (SELECT y FROM bar)",
///   "STATEMENT: CREATE TABLE baz (q INT)"
/// ]
///   .into_iter().map(|s| s.to_string()).collect();
///
/// assert_eq!(visited, expected);
/// ```
pub fn visit_statements<V, E, F>(v: &V, f: F) -> ControlFlow<E>
where
    V: Visit,
    F: FnMut(&Statement) -> ControlFlow<E>,
{
    let mut visitor = StatementVisitor(f);
    v.visit(&mut visitor)?;
    ControlFlow::Continue(())
}

/// Invokes the provided closure on all statements (e.g. `SELECT`, `CREATE TABLE`, etc) present in `v`
///
/// # Example
/// ```
/// # use sqlparser::parser::Parser;
/// # use sqlparser::dialect::GenericDialect;
/// # use sqlparser::ast::{Statement, visit_statements_mut};
/// # use core::ops::ControlFlow;
/// let sql = "SELECT x FROM foo LIMIT 9+$limit; SELECT * FROM t LIMIT f()";
/// let mut statements = Parser::parse_sql(&GenericDialect{}, sql).unwrap();
///
/// // Remove all select limits in outer statements (not in sub-queries)
/// visit_statements_mut(&mut statements, |stmt| {
///   if let Statement::Query(q) = stmt {
///      q.limit_clause = None;
///   }
///   ControlFlow::<()>::Continue(())
/// });
///
/// assert_eq!(statements[0].to_string(), "SELECT x FROM foo");
/// assert_eq!(statements[1].to_string(), "SELECT * FROM t");
/// ```
pub fn visit_statements_mut<V, E, F>(v: &mut V, f: F) -> ControlFlow<E>
where
    V: VisitMut,
    F: FnMut(&mut Statement) -> ControlFlow<E>,
{
    v.visit(&mut StatementVisitor(f))?;
    ControlFlow::Continue(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Statement;
    use crate::dialect::GenericDialect;
    use crate::parser::Parser;
    use crate::tokenizer::Tokenizer;

    #[derive(Default)]
    struct TestVisitor {
        visited: Vec<String>,
    }

    impl Visitor for TestVisitor {
        type Break = ();

        /// Invoked for any queries that appear in the AST before visiting children
        fn pre_visit_query(&mut self, query: &Query) -> ControlFlow<Self::Break> {
            self.visited.push(format!("PRE: QUERY: {query}"));
            ControlFlow::Continue(())
        }

        /// Invoked for any queries that appear in the AST after visiting children
        fn post_visit_query(&mut self, query: &Query) -> ControlFlow<Self::Break> {
            self.visited.push(format!("POST: QUERY: {query}"));
            ControlFlow::Continue(())
        }

        fn pre_visit_relation(&mut self, relation: &ObjectName) -> ControlFlow<Self::Break> {
            self.visited.push(format!("PRE: RELATION: {relation}"));
            ControlFlow::Continue(())
        }

        fn post_visit_relation(&mut self, relation: &ObjectName) -> ControlFlow<Self::Break> {
            self.visited.push(format!("POST: RELATION: {relation}"));
            ControlFlow::Continue(())
        }

        fn pre_visit_table_factor(
            &mut self,
            table_factor: &TableFactor,
        ) -> ControlFlow<Self::Break> {
            self.visited
                .push(format!("PRE: TABLE FACTOR: {table_factor}"));
            ControlFlow::Continue(())
        }

        fn post_visit_table_factor(
            &mut self,
            table_factor: &TableFactor,
        ) -> ControlFlow<Self::Break> {
            self.visited
                .push(format!("POST: TABLE FACTOR: {table_factor}"));
            ControlFlow::Continue(())
        }

        fn pre_visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::Break> {
            self.visited.push(format!("PRE: EXPR: {expr}"));
            ControlFlow::Continue(())
        }

        fn post_visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::Break> {
            self.visited.push(format!("POST: EXPR: {expr}"));
            ControlFlow::Continue(())
        }

        fn pre_visit_statement(&mut self, statement: &Statement) -> ControlFlow<Self::Break> {
            self.visited.push(format!("PRE: STATEMENT: {statement}"));
            ControlFlow::Continue(())
        }

        fn post_visit_statement(&mut self, statement: &Statement) -> ControlFlow<Self::Break> {
            self.visited.push(format!("POST: STATEMENT: {statement}"));
            ControlFlow::Continue(())
        }
    }

    fn do_visit<V: Visitor>(sql: &str, visitor: &mut V) -> Statement {
        let dialect = GenericDialect {};
        let tokens = Tokenizer::new(&dialect, sql).tokenize().unwrap();
        let s = Parser::new(&dialect)
            .with_tokens(tokens)
            .parse_statement()
            .unwrap();

        s.visit(visitor);
        s
    }

    #[test]
    fn test_sql() {
        let tests = vec![
            (
                "SELECT * from table_name as my_table",
                vec![
                    "PRE: STATEMENT: SELECT * FROM table_name AS my_table",
                    "PRE: QUERY: SELECT * FROM table_name AS my_table",
                    "PRE: TABLE FACTOR: table_name AS my_table",
                    "PRE: RELATION: table_name",
                    "POST: RELATION: table_name",
                    "POST: TABLE FACTOR: table_name AS my_table",
                    "POST: QUERY: SELECT * FROM table_name AS my_table",
                    "POST: STATEMENT: SELECT * FROM table_name AS my_table",
                ],
            ),
            (
                "SELECT * from t1 join t2 on t1.id = t2.t1_id",
                vec![
                    "PRE: STATEMENT: SELECT * FROM t1 JOIN t2 ON t1.id = t2.t1_id",
                    "PRE: QUERY: SELECT * FROM t1 JOIN t2 ON t1.id = t2.t1_id",
                    "PRE: TABLE FACTOR: t1",
                    "PRE: RELATION: t1",
                    "POST: RELATION: t1",
                    "POST: TABLE FACTOR: t1",
                    "PRE: TABLE FACTOR: t2",
                    "PRE: RELATION: t2",
                    "POST: RELATION: t2",
                    "POST: TABLE FACTOR: t2",
                    "PRE: EXPR: t1.id = t2.t1_id",
                    "PRE: EXPR: t1.id",
                    "POST: EXPR: t1.id",
                    "PRE: EXPR: t2.t1_id",
                    "POST: EXPR: t2.t1_id",
                    "POST: EXPR: t1.id = t2.t1_id",
                    "POST: QUERY: SELECT * FROM t1 JOIN t2 ON t1.id = t2.t1_id",
                    "POST: STATEMENT: SELECT * FROM t1 JOIN t2 ON t1.id = t2.t1_id",
                ],
            ),
            (
                "SELECT * from t1 where EXISTS(SELECT column from t2)",
                vec![
                    "PRE: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "PRE: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "PRE: TABLE FACTOR: t1",
                    "PRE: RELATION: t1",
                    "POST: RELATION: t1",
                    "POST: TABLE FACTOR: t1",
                    "PRE: EXPR: EXISTS (SELECT column FROM t2)",
                    "PRE: QUERY: SELECT column FROM t2",
                    "PRE: EXPR: column",
                    "POST: EXPR: column",
                    "PRE: TABLE FACTOR: t2",
                    "PRE: RELATION: t2",
                    "POST: RELATION: t2",
                    "POST: TABLE FACTOR: t2",
                    "POST: QUERY: SELECT column FROM t2",
                    "POST: EXPR: EXISTS (SELECT column FROM t2)",
                    "POST: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "POST: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                ],
            ),
            (
                "SELECT * from t1 where EXISTS(SELECT column from t2)",
                vec![
                    "PRE: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "PRE: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "PRE: TABLE FACTOR: t1",
                    "PRE: RELATION: t1",
                    "POST: RELATION: t1",
                    "POST: TABLE FACTOR: t1",
                    "PRE: EXPR: EXISTS (SELECT column FROM t2)",
                    "PRE: QUERY: SELECT column FROM t2",
                    "PRE: EXPR: column",
                    "POST: EXPR: column",
                    "PRE: TABLE FACTOR: t2",
                    "PRE: RELATION: t2",
                    "POST: RELATION: t2",
                    "POST: TABLE FACTOR: t2",
                    "POST: QUERY: SELECT column FROM t2",
                    "POST: EXPR: EXISTS (SELECT column FROM t2)",
                    "POST: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                    "POST: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2)",
                ],
            ),
            (
                "SELECT * from t1 where EXISTS(SELECT column from t2) UNION SELECT * from t3",
                vec![
                    "PRE: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2) UNION SELECT * FROM t3",
                    "PRE: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2) UNION SELECT * FROM t3",
                    "PRE: TABLE FACTOR: t1",
                    "PRE: RELATION: t1",
                    "POST: RELATION: t1",
                    "POST: TABLE FACTOR: t1",
                    "PRE: EXPR: EXISTS (SELECT column FROM t2)",
                    "PRE: QUERY: SELECT column FROM t2",
                    "PRE: EXPR: column",
                    "POST: EXPR: column",
                    "PRE: TABLE FACTOR: t2",
                    "PRE: RELATION: t2",
                    "POST: RELATION: t2",
                    "POST: TABLE FACTOR: t2",
                    "POST: QUERY: SELECT column FROM t2",
                    "POST: EXPR: EXISTS (SELECT column FROM t2)",
                    "PRE: TABLE FACTOR: t3",
                    "PRE: RELATION: t3",
                    "POST: RELATION: t3",
                    "POST: TABLE FACTOR: t3",
                    "POST: QUERY: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2) UNION SELECT * FROM t3",
                    "POST: STATEMENT: SELECT * FROM t1 WHERE EXISTS (SELECT column FROM t2) UNION SELECT * FROM t3",
                ],
            ),
            (
                concat!(
                    "SELECT * FROM monthly_sales ",
                    "PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ",
                    "ORDER BY EMPID"
                ),
                vec![
                    "PRE: STATEMENT: SELECT * FROM monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ORDER BY EMPID",
                    "PRE: QUERY: SELECT * FROM monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ORDER BY EMPID",
                    "PRE: TABLE FACTOR: monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d)",
                    "PRE: TABLE FACTOR: monthly_sales",
                    "PRE: RELATION: monthly_sales",
                    "POST: RELATION: monthly_sales",
                    "POST: TABLE FACTOR: monthly_sales",
                    "PRE: EXPR: SUM(a.amount)",
                    "PRE: EXPR: a.amount",
                    "POST: EXPR: a.amount",
                    "POST: EXPR: SUM(a.amount)",
                    "PRE: EXPR: 'JAN'",
                    "POST: EXPR: 'JAN'",
                    "PRE: EXPR: 'FEB'",
                    "POST: EXPR: 'FEB'",
                    "PRE: EXPR: 'MAR'",
                    "POST: EXPR: 'MAR'",
                    "PRE: EXPR: 'APR'",
                    "POST: EXPR: 'APR'",
                    "POST: TABLE FACTOR: monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d)",
                    "PRE: EXPR: EMPID",
                    "POST: EXPR: EMPID",
                    "POST: QUERY: SELECT * FROM monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ORDER BY EMPID",
                    "POST: STATEMENT: SELECT * FROM monthly_sales PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ORDER BY EMPID",
                ]
            ),
            (
                "SHOW COLUMNS FROM t1",
                vec![
                    "PRE: STATEMENT: SHOW COLUMNS FROM t1",
                    "PRE: RELATION: t1",
                    "POST: RELATION: t1",
                    "POST: STATEMENT: SHOW COLUMNS FROM t1",
                ],
            ),
        ];
        for (sql, expected) in tests {
            let mut visitor = TestVisitor::default();
            let _ = do_visit(sql, &mut visitor);
            let actual: Vec<_> = visitor.visited.iter().map(|x| x.as_str()).collect();
            assert_eq!(actual, expected)
        }
    }

    struct QuickVisitor; // [`TestVisitor`] is too slow to iterate over thousands of nodes

    impl Visitor for QuickVisitor {
        type Break = ();
    }

    #[test]
    fn overflow() {
        let cond = (0..1000)
            .map(|n| format!("X = {}", n))
            .collect::<Vec<_>>()
            .join(" OR ");
        let sql = format!("SELECT x where {0}", cond);

        let dialect = GenericDialect {};
        let tokens = Tokenizer::new(&dialect, sql.as_str()).tokenize().unwrap();
        let s = Parser::new(&dialect)
            .with_tokens(tokens)
            .parse_statement()
            .unwrap();

        let mut visitor = QuickVisitor {};
        s.visit(&mut visitor);
    }
}

#[cfg(test)]
mod visit_mut_tests {
    use crate::ast::{Statement, Value, VisitMut, VisitorMut};
    use crate::dialect::GenericDialect;
    use crate::parser::Parser;
    use crate::tokenizer::Tokenizer;
    use core::ops::ControlFlow;

    #[derive(Default)]
    struct MutatorVisitor {
        index: u64,
    }

    impl VisitorMut for MutatorVisitor {
        type Break = ();

        fn pre_visit_value(&mut self, value: &mut Value) -> ControlFlow<Self::Break> {
            self.index += 1;
            *value = Value::SingleQuotedString(format!("REDACTED_{}", self.index));
            ControlFlow::Continue(())
        }

        fn post_visit_value(&mut self, _value: &mut Value) -> ControlFlow<Self::Break> {
            ControlFlow::Continue(())
        }
    }

    fn do_visit_mut<V: VisitorMut>(sql: &str, visitor: &mut V) -> Statement {
        let dialect = GenericDialect {};
        let tokens = Tokenizer::new(&dialect, sql).tokenize().unwrap();
        let mut s = Parser::new(&dialect)
            .with_tokens(tokens)
            .parse_statement()
            .unwrap();

        s.visit(visitor);
        s
    }

    #[test]
    fn test_value_redact() {
        let tests = vec![
            (
                concat!(
                    "SELECT * FROM monthly_sales ",
                    "PIVOT(SUM(a.amount) FOR a.MONTH IN ('JAN', 'FEB', 'MAR', 'APR')) AS p (c, d) ",
                    "ORDER BY EMPID"
                ),
                concat!(
                    "SELECT * FROM monthly_sales ",
                    "PIVOT(SUM(a.amount) FOR a.MONTH IN ('REDACTED_1', 'REDACTED_2', 'REDACTED_3', 'REDACTED_4')) AS p (c, d) ",
                    "ORDER BY EMPID"
                ),
            ),
        ];

        for (sql, expected) in tests {
            let mut visitor = MutatorVisitor::default();
            let mutated = do_visit_mut(sql, &mut visitor);
            assert_eq!(mutated.to_string(), expected)
        }
    }
}
