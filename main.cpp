#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <winsock2.h>
#include <ws2tcpip.h>
#include <algorithm>
#include <set>
#include <map>
#include <cstdio>
#include <cctype>

// LINKER INSTRUCTION: You MUST add "-lws2_32" to the linker parameters in Dev-C++.

using namespace std;

// ==========================================
//          STRING & LOGIC UTILITIES
// ==========================================

struct ProofStep {
    int lineNum;
    string statement;
    string rule;
    string references; // stored as "1, 2"
};

string normalize(string s) {
    string res = "";
    for (size_t i = 0; i < s.length(); ++i) {
        if (s[i] == ' ') continue;
        if (s[i] == '-' && i+1 < s.length() && s[i+1] == '>') { res += '>'; i++; }
        else if (s[i] == '<' && i+2 < s.length() && s[i+1] == '-' && s[i+2] == '>') { res += '='; i += 2; }
        else if (tolower(s[i]) == 'v') { res += '|'; }
        else if (s[i] == '^') { res += '&'; }
        else { res += s[i]; }
    }
    return res;
}

string strip(string s) {
    while (s.length() > 2 && s.front() == '(' && s.back() == ')') {
        int depth = 0;
        bool clean = true;
        for (size_t i = 0; i < s.length() - 1; ++i) {
            if (s[i] == '(') depth++;
            else if (s[i] == ')') depth--;
            if (depth == 0) { clean = false; break; }
        }
        if (clean) s = s.substr(1, s.length() - 2);
        else break;
    }
    return s;
}

bool splitOp(string s, char op, string& L, string& R) {
    s = strip(s);
    int depth = 0;
    for (size_t i = 0; i < s.length(); ++i) {
        if (s[i] == '(') depth++;
        else if (s[i] == ')') depth--;
        else if (depth == 0 && s[i] == op) {
            L = strip(s.substr(0, i));
            R = strip(s.substr(i + 1));
            return true;
        }
    }
    return false;
}

bool isNot(string s, string& inner) {
    s = strip(s);
    if (s.length() > 0 && s[0] == '~') {
        inner = strip(s.substr(1));
        return true;
    }
    return false;
}

string urlDecode(string str) {
    string res;
    for (size_t i = 0; i < str.length(); ++i) {
        if (str[i] == '%') {
            if (i + 2 < str.length()) {
                int val; sscanf(str.substr(i + 1, 2).c_str(), "%x", &val);
                res += (char)val; i += 2;
            }
        } else if (str[i] == '+') res += ' ';
        else res += str[i];
    }
    return res;
}

// ==========================================
//          THE LOGIC ENGINE
// ==========================================

class LogicEngine {
    vector<ProofStep> proof;
    set<string> known;
    string target;
    
public:
    void setTarget(string s) {
        target = normalize(s);
        target = strip(target);
    }
    
    void addPremise(string s) {
        s = normalize(s);
        s = strip(s);
        if(known.count(s)) return;
        proof.push_back({(int)proof.size()+1, s, "Premise", ""});
        known.insert(s);
    }
    
    // Core Add function
    bool add(string s, string rule, string refs) {
        s = strip(s);
        if(known.count(s)) return false;
        proof.push_back({(int)proof.size()+1, s, rule, refs});
        known.insert(s);
        return (s == target);
    }
    
    // --- THE PRUNING SYSTEM ---
    // Recursively finds which lines were actually used
    void markUsed(int lineNum, set<int>& used, const map<int, ProofStep>& lookup) {
        if(used.count(lineNum)) return;
        used.insert(lineNum);
        
        if(lookup.find(lineNum) == lookup.end()) return;
        string refs = lookup.at(lineNum).references;
        
        stringstream ss(refs);
        string segment;
        while(getline(ss, segment, ',')) {
            if(!segment.empty()) {
                markUsed(stoi(segment), used, lookup);
            }
        }
    }

    string solve() {
        int idx = 0;
        int maxSteps = 300; 
        
        // 1. GENERATE (The dirty phase)
        bool success = false;
        while(idx < proof.size() && proof.size() < maxSteps) {
            if(known.count(target)) { success = true; break; }
            
            // Priority 1: Inference
            for(int i=0; i<=idx; i++) { applyDouble(i, idx); if(i!=idx) applyDouble(idx, i); }
            // Priority 2: Replacement
            applySingle(idx);
            // Priority 3: Heuristics
            string P = proof[idx].statement;
            string ref = to_string(proof[idx].lineNum);
            
            // Addition
            string L, R;
            if(splitOp(target, '|', L, R)) {
                if(L == P || strip(L) == P) add(target, "Addition", ref);
                else if(R == P || strip(R) == P) add(target, "Addition", ref);
            }
            // Conjunction for CD
            if(splitOp(target, '&', L, R)) {
                if((L == P && known.count(R)) || (R == P && known.count(L))) {
                    string other = (L == P) ? R : L;
                    string otherRef = "";
                    for(auto& step : proof) if(step.statement == other) { otherRef = to_string(step.lineNum); break; }
                    add(target, "Conjunction", ref + ", " + otherRef);
                }
            }
            idx++;
        }
        
        if(!known.count(target)) return "{\"status\":\"fail\"}";

        // 2. PRUNE & RENUMBER (The cleaning phase)
        // Map current line numbers to steps
        map<int, ProofStep> lookup;
        int targetLine = -1;
        for(auto& s : proof) {
            lookup[s.lineNum] = s;
            if(s.statement == target) targetLine = s.lineNum;
        }

        // Trace back from target
        set<int> usedLines;
        markUsed(targetLine, usedLines, lookup);

        // Build new clean proof
        vector<ProofStep> cleanProof;
        map<int, int> oldToNew; // Map old line num -> new line num

        int newLineCounter = 1;
        for(auto& s : proof) {
            if(usedLines.count(s.lineNum)) {
                ProofStep cleanStep = s;
                cleanStep.lineNum = newLineCounter;
                oldToNew[s.lineNum] = newLineCounter;
                
                // Update references to point to new line numbers
                if(!s.references.empty()) {
                    string newRefs = "";
                    stringstream ss(s.references);
                    string refSeg;
                    while(getline(ss, refSeg, ',')) {
                        if(!refSeg.empty()) {
                            int oldRef = stoi(refSeg);
                            if(oldToNew.count(oldRef)) {
                                if(newRefs.length() > 0) newRefs += ", ";
                                newRefs += to_string(oldToNew[oldRef]);
                            }
                        }
                    }
                    cleanStep.references = newRefs;
                }
                
                cleanProof.push_back(cleanStep);
                newLineCounter++;
            }
        }

        // 3. OUTPUT JSON
        stringstream ss;
        ss << "{\"status\":\"success\",\"steps\":[";
        for(size_t i=0; i<cleanProof.size(); i++) {
            ss << "{\"line\":" << cleanProof[i].lineNum << ",\"statement\":\"" << cleanProof[i].statement 
               << "\",\"rule\":\"" << cleanProof[i].rule << "\",\"refs\":\"" << cleanProof[i].references << "\"}";
            if(i < cleanProof.size()-1) ss << ",";
        }
        ss << "]}";
        return ss.str();
    }
    
    void applySingle(int i) {
        string S = proof[i].statement;
        string ref = to_string(proof[i].lineNum);
        string A, B, C, X, Y;
        
        // Simplification
        if(splitOp(S, '&', A, B)) { add(A, "Simplification", ref); add(B, "Simplification", ref); }
        
        // Double Negation (Reduction only)
        if(isNot(S, X) && isNot(X, Y)) add(Y, "Double Negation", ref);
        
        // De Morgan
        if(isNot(S, X)) {
            if(splitOp(X, '&', A, B)) add("~"+A+"|~"+B, "De Morgan", ref);
            if(splitOp(X, '|', A, B)) add("~"+A+"&~"+B, "De Morgan", ref);
        }
        string nA, nB, realA, realB;
        if(splitOp(S, '|', nA, nB)) if(isNot(nA, realA) && isNot(nB, realB)) add("~(" + realA + "&" + realB + ")", "De Morgan", ref);
        if(splitOp(S, '&', nA, nB)) if(isNot(nA, realA) && isNot(nB, realB)) add("~(" + realA + "|" + realB + ")", "De Morgan", ref);
        
        // Contraposition (Strict no-loop)
        if(splitOp(S, '>', A, B)) {
            if(A.find("~~") == string::npos && B.find("~~") == string::npos) add("~"+B+">~"+A, "Contraposition", ref);
        }
        
        // Commutation
        if(splitOp(S, '|', A, B)) add(B+"|"+A, "Commutation", ref);
        if(splitOp(S, '&', A, B)) add(B+"&"+A, "Commutation", ref);
        
        // Association
        if(splitOp(S, '&', X, C) && splitOp(X, '&', A, B)) add(A+"&("+B+"&"+C+")", "Association", ref);
        if(splitOp(S, '|', X, C) && splitOp(X, '|', A, B)) add(A+"|("+B+"|"+C+")", "Association", ref);
        
        // Distribution
        if(splitOp(S, '&', A, X) && splitOp(X, '|', B, C)) add("("+A+"&"+B+")|("+A+"&"+C+")", "Distribution", ref);
        if(splitOp(S, '|', A, X) && splitOp(X, '&', B, C)) add("("+A+"|"+B+")&("+A+"|"+C+")", "Distribution", ref);
        if(splitOp(S, '&', X, A) && splitOp(X, '|', B, C)) add("("+B+"&"+A+")|("+C+"&"+A+")", "Distribution", ref);

        // Biconditional
        if(splitOp(S, '=', A, B)) {
            add("("+A+">"+B+")&("+B+">"+A+")", "Biconditional Equiv", ref);
            add("("+A+"&"+B+")|(~"+A+"&~"+B+")", "Biconditional Equiv", ref);
        }
    }
    
    void applyDouble(int i, int j) {
        string S1 = proof[i].statement;
        string S2 = proof[j].statement;
        string refs = to_string(proof[i].lineNum) + ", " + to_string(proof[j].lineNum);
        string P, Q, notQ, p1, q1, r1, s1, imp1, imp2, orL, orR;
        
        if(splitOp(S1, '>', P, Q) && P == S2) add(Q, "Modus Ponens", refs);
        
        if(splitOp(S1, '>', P, Q)) {
            notQ = "~" + strip(Q);
            if(S2 == notQ) add("~"+P, "Modus Tollens", refs);
        }
        
        string Q_HS, R_HS;
        if(splitOp(S1, '>', P, Q) && splitOp(S2, '>', Q_HS, R_HS) && Q == Q_HS) add(P + ">" + R_HS, "Hypothetical Syllogism", refs);
            
        if(splitOp(S1, '|', P, Q)) {
            string notP = "~" + strip(P);
            string notQ_DS = "~" + strip(Q);
            if(S2 == notP) add(Q, "Disjunctive Syllogism", refs);
            if(S2 == notQ_DS) add(P, "Disjunctive Syllogism", refs);
        }
        
        if(splitOp(S1, '|', P, Q) && splitOp(S2, '|', r1, s1)) {
            string notP = "~" + strip(P);
            if(r1 == notP) add(Q + "|" + s1, "Resolution", refs);
        }
        
        if(splitOp(S1, '&', imp1, imp2)) {
            if(splitOp(imp1, '>', p1, q1) && splitOp(imp2, '>', r1, s1)) {
                if(splitOp(S2, '|', orL, orR)) {
                    if((orL == p1 && orR == r1) || (orL == r1 && orR == p1)) add(q1 + "|" + s1, "Constructive Dilemma", refs);
                }
            }
        }
        
        if(splitOp(S1, '>', p1, q1) && splitOp(S2, '>', r1, s1)) {
            string needed = p1 + "|" + r1;
            if(known.count(needed)) add("("+S1+")&("+S2+")", "Conjunction", refs);
        }
    }
};

// ==========================================
//          SERVER HANDLING
// ==========================================

void sendResp(SOCKET s, string body, string type) {
    string h = "HTTP/1.1 200 OK\r\nAccess-Control-Allow-Origin: *\r\nContent-Type: "+type+"\r\nContent-Length: "+to_string(body.size())+"\r\n\r\n" + body;
    send(s, h.c_str(), h.size(), 0);
}

int main() {
    WSADATA wsa; 
    if(WSAStartup(MAKEWORD(2,2), &wsa) != 0) { cout << "WSA Error" << endl; return 1; }
    
    // Changed port to 8081 to avoid conflict with stuck 8080 processes
    SOCKET s = socket(AF_INET, SOCK_STREAM, 0);
    sockaddr_in a; a.sin_family = AF_INET; a.sin_port = htons(8081); a.sin_addr.s_addr = INADDR_ANY;
    
    if(bind(s, (sockaddr*)&a, sizeof(a)) == SOCKET_ERROR) { cout << "Bind Error (Port 8081)" << endl; return 1; }
    listen(s, SOMAXCONN);
    
    cout << "LOGIC ENGINE ON PORT 8081. Update HTML to http://localhost:8081" << endl;
    
    while(true) {
        SOCKET c = accept(s, 0, 0);
        if(c == INVALID_SOCKET) continue;
        char buf[8192] = {0}; 
        int bytes = recv(c, buf, 8192, 0);
        if(bytes <= 0) { closesocket(c); continue; }
        string req(buf);
        
        if(req.find("GET / ") != string::npos) {
            FILE* f = fopen("index.html", "rb");
            if(f) {
                fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
                string html(sz, 0); fread(&html[0], 1, sz, f); fclose(f);
                sendResp(c, html, "text/html");
            } else sendResp(c, "<h1>index.html missing</h1>", "text/html");
        }
        else if(req.find("POST /solve") != string::npos) {
            string body = "";
            size_t bodyPos = req.find("\r\n\r\n");
            if(bodyPos != string::npos) body = req.substr(bodyPos + 4);
            size_t pPos = body.find("premises=");
            size_t cPos = body.find("&conclusion=");
            if(pPos != string::npos && cPos != string::npos) {
                string pRaw = urlDecode(body.substr(pPos+9, cPos-(pPos+9)));
                string cRaw = urlDecode(body.substr(cPos+12));
                LogicEngine engine;
                engine.setTarget(cRaw);
                stringstream ss(pRaw); string line;
                while(getline(ss, line, '\n')) {
                     if (!line.empty() && line.back() == '\r') line.pop_back();
                     if(!line.empty()) engine.addPremise(line);
                }
                sendResp(c, engine.solve(), "application/json");
            }
        }
        closesocket(c);
    }
    return 0;
}
