#include <cstdio>
#include <cstdlib>

#include <vector>
#include <tuple>
#include <unordered_map>
#include <istream>
#include <fstream>

#define SELF 0

#define ATOM 0
#define RVAR 1
#define VAR  2

#define BUFMAX 256

struct Item { std::string dat; int type;
              Item(std::string _d, int _t) {
                dat = _d; type = _t; }
              Item() { type = ATOM; } };
/*void item_print(Item a) {
  if(a->type == GRP) { printf("(");
    for(int i=0;i<a->grp.size();i++) { item_print(a->grp[i]); }
    printf (")"); } else { printf(" %s ",a->dat.c_str()); } }*/
void p_stk(std::vector<Item> a) {
  for(int i=0;i<a.size();i++) { printf("%s ",a[i].dat.c_str()); } printf("\n"); }
bool operator==(Item a, Item b) { if(a.type!=b.type&&a.type!=VAR &&b.type!=VAR
                                                   &&a.type!=RVAR&&b.type!=RVAR) { return false; }
  switch(b.type) { case ATOM: return a.dat==b.dat; break;
                   case RVAR: return false; break; // not supported yet.
                   case VAR: return true; } }
// typedef std::vector<Item> Stk;
struct Term { std::string var; std::vector<Item> r;
              Term(std::string _v, std::vector<Item> _r) { var = _v; r = _r; }
              Term() { } };
struct Rule { int loc; std::vector<Item> in; std::vector<Item> out;
              std::unordered_map<std::string,std::vector<Item>> ts; int exprn;
              Rule(std::vector<Item> _in, std::vector<Item> _out) {
                ts = std::unordered_map<std::string,std::vector<Item>>();
                in = _in, out = _out; exprn = 0; loc = 0; } };
Item rules_loc(Rule r, int loc) { return r.in[loc]; }

std::vector<Rule> d_rules = { Rule((std::vector<Item>){ Item("Just",ATOM), Item("$a",VAR) }
                                  ,(std::vector<Item>){ Item("$a",VAR) }) };

std::vector<Item> exec_rule(std::vector<Item> expr, std::vector<Rule> rules, Rule a) {
  /*p_stk(expr); p_stk(a.in); return a.out;*/
  std::vector<Item> ret;
  for(int i=0;i<a.out.size();i++) {
    if(a.out[i].type==VAR) { auto q = a.ts[a.out[i].dat];
                             ret.insert(ret.end(),q.begin(),q.end()); }
    else { ret.push_back(a.out[i]); } }
  int q = 0; int exprn = 0;
  for(int i=0;i<a.in.size();q++) { if(expr[expr.size()-1-q].dat=="(") { exprn--; }
    else if(expr[expr.size()-1-q].dat==")") { exprn++; }
    if(!exprn) { i++; } }
  expr.erase(expr.begin(),expr.end()-q); return expr; }

// modifies locs
// warning: not well written
std::vector<Item> match_rule(std::vector<Item> expr, Item q, std::vector<Rule> &rules, std::vector<int> &locs) {
  for(int i=0;i<rules.size();i++) {
    if(q==rules_loc(rules[i],locs[i])) {
      if(rules_loc(rules[i],locs[i]).type==VAR) { if(q.dat=="(") { rules[i].exprn++; }
        else if(q.dat==")") { rules[i].exprn--; }
        //else if(rules[i].exprn) { rules[i].ts[rules_loc(rules[i],locs[i]).dat].push_back(q); }
        rules[i].ts[rules_loc(rules[i],locs[i]).dat].push_back(q);
        if(!rules[i].exprn) { locs[i]++; } }
      else { locs[i]++; } }
    else { locs[i] = 0; }
    if(locs[i]>=rules[i].in.size()) {
      locs[i] = 0; expr.push_back(q);
      expr = exec_rule(expr,rules,rules[i]); rules[i] = Rule(rules[i].in,rules[i].out); return expr; } }
  expr.push_back(q); return expr; }

std::vector<Item> lex_and_parse(std::ifstream &a, std::vector<Rule> rules, std::vector<Item> vars) {
  auto locs = std::vector<int>(rules.size(),0);
  for(int i=0;i<locs.size();i++) { locs[i] = rules[i].loc; }
  a >> std::ws; std::vector<Item> expr;
  while(!a.eof()) { a >> std::ws; switch(a.peek()) {
    case ')': { a.ignore(1); expr = match_rule(expr,Item(")",ATOM),rules,locs);
                break; }
    case '(': { a.ignore(1); expr = match_rule(expr,Item("(",ATOM),rules,locs);
                break; }
    case '$': { std::string q; a >> q; if(q.back()==')') { q.pop_back(); a.putback(')'); }
                expr = match_rule(expr,Item(q,VAR),rules,locs); break; }
    case '[': { a.ignore(1); char *qc; a.get(qc,BUFMAX,']'); a.ignore(1); std::string qr(qc);
                std::string q; a >> q; qr += " " + q;
                expr = match_rule(expr,Item(qr,RVAR),rules,locs); break; }
    default: { std::string q; a >> q; if(q.back()==')') { q.pop_back(); a.putback(')'); }
               expr = match_rule(expr,Item(q,ATOM),rules,locs); break; } } }
  return expr; }

int main(int argc, char **argv) {
  std::ifstream file; file.open(argv[1]);
  std::vector<Item> f = lex_and_parse(file,d_rules,std::vector<Item>());
  p_stk(f);
  /*item_destroy(f);*/ return 0; }
