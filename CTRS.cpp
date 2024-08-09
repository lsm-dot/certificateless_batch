#include <iostream>
#include <chrono>
#include <ctime>
#include <vector>
#include <sstream>
#include <fstream>

// Security define
#define AES_SECURITY 80
#define MR_PAIRING_SSP
#include "pairing_1.h"


using namespace std;
extern "C" {
#include "miracl.h"
#include "mirdef.h"
}

struct KeyParams
{
    Big q;
    G1 P;
};

struct Sigma
{
    Big huk;
    pair<Big, G1> Ak;
    G1 U;
    G1 V;
};

Big H11(KeyParams& params, PFC& pfc, char* IDi) {
    Big result;
    result = pfc.hash_to_group(IDi);
    return result;
}

Big H2(KeyParams& params, PFC& pfc, char* mk, char* R, G1& Qk, G1& PSKk, pair<G1, G1>& PKk, Big& rk) {
    Big mk_big, R_big;
    
    mk_big = pfc.hash_to_group(mk);
    R_big = pfc.hash_to_group(R);
    pfc.start_hash();
    pfc.add_to_hash(mk_big);
    pfc.add_to_hash(R_big);
    pfc.add_to_hash(Qk);
    pfc.add_to_hash(PSKk);
    pfc.add_to_hash(PKk.first);
    pfc.add_to_hash(PKk.second);
    pfc.add_to_hash(rk);
    Big result = pfc.finish_hash_to_group();
    //Big result = mk_big + R_big + sumAdd + rk;
    return result;
}

Big H3(KeyParams& params, PFC& pfc, char* mk, pair<Big, G1>& Ak, G1& Ui) {
    Big mk_big = pfc.hash_to_group(mk);
    pfc.start_hash();
    pfc.add_to_hash(mk_big);
    pfc.add_to_hash(Ak.first);
    pfc.add_to_hash(Ak.second);
    pfc.add_to_hash(Ui);
    Big result = pfc.finish_hash_to_group();
    //Big result = mk_big + Ak.first + sumAdd;
    return result;
}

Big H4(KeyParams& params, PFC& pfc, char* mk, vector<char*> Lid, vector<pair<G1, G1>>& Lpk, Big& huk) {
    int length = Lid.size();
    Big mk_big = pfc.hash_to_group(mk);
    pfc.start_hash();
    pfc.add_to_hash(mk_big);
    /*Big result = mk_big;*/
    for (int i = 0; i < length; i++)
    {
        Big temp = pfc.hash_to_group(Lid[i]);
        pfc.add_to_hash(temp);
        //pfc.start_hash();
        pfc.add_to_hash(Lpk[i].first);
        pfc.add_to_hash(Lpk[i].second);
        //Big temp = pfc.finish_hash_to_group();
        //result += temp;
    }
    pfc.add_to_hash(huk);
    Big result = pfc.finish_hash_to_group();
    return result;
}

void KeyGen(KeyParams& params, PFC& pfc, Big& SKtrc, vector<char*> ID, vector<pair<G1, G1>>& PP, vector<G1>& SK, vector<pair<G1, G1>>& PK) {
    int length = ID.size();
    G1 P = params.P;
    vector<Big> q(length);
    vector<G1> Q(length);
    vector<G1> Qi(length);
    vector<G1> PSK(length);
    SK.resize(length);
    PK.resize(length);
    
    for (int i = 0; i < length; i++)
    {
        q[i] = H11(params, pfc, ID[i]);
        Q[i] = pfc.mult(P, q[i]);
        PSK[i] = pfc.mult(P, SKtrc * q[i]);
        Big wi;
        pfc.random(wi);
        Qi[i] = pfc.mult(P, wi * q[i]);   // trace ring secret for ring member IDi
        PP[i] = { PSK[i], Qi[i] };

        Big xi;
        pfc.random(xi);
        Big temp = inverse(xi + q[i], params.q);
        //temp /= (xi + q[i]);
        SK[i] = pfc.mult(PSK[i], temp);
        G1 Yi = pfc.mult(Q[i], temp);
        G1 Xi = pfc.mult(P, temp);
        G1 Xii = Xi + pfc.mult(Qi[i], q[i]);
        PK[i] = { Yi, Xii };
    }
}

Sigma sign(KeyParams& params, PFC& pfc, char* R, vector<char*> ID, vector<pair<G1, G1>>& PK, G1& SKk, pair<G1, G1>& PPk, int k,  char* m, G1& PKtrc) {
    int length = ID.size();
    Big rk;
    pfc.random(rk);
    Big h0k = H2(params, pfc, m, R, PPk.second, PPk.first, PK[k], rk);
    Big ak = inverse(rk + h0k, params.q);
    //ak /= (rk + h0k);
    G1 Akk = pfc.mult(PK[k].second, ak);
    pair<Big, G1> Ak = { ak, Akk };
    G1 Uk = pfc.mult(PK[k].first, ak);
    Big huk = 0;

    for (int i = 0; i < length; i++)
    {
        if (i == k)
        {
            continue;
        }
        G1 Ui;
        pfc.random(Ui);
        Big hui = H3(params, pfc, m, Ak, Ui);
        huk += hui;
    }
    Big h1k = H4(params, pfc, m, ID, PK, huk);
    Big inverse_h1k = inverse(h1k, params.q);
    G1 Vk = pfc.mult(SKk, ak);
    G1 temp_Vk = pfc.mult(PKtrc, inverse_h1k);
    Vk = Vk + temp_Vk;
        
    return { huk, Ak, Uk, Vk };

}

bool singleVerify(KeyParams& params, PFC& pfc, char* R, vector<char*> ID, vector<pair<G1, G1>>& PK, char* m, Sigma& sigma, G1& PKtrc) {
    Big huk = sigma.huk;
    G1 Uk = sigma.U;
    G1 Vk = sigma.V;
    G1 P = params.P;
    Big h1k = H4(params, pfc, m, ID, PK, huk);
    Big inverse_h1k = inverse(h1k, params.q);
    GT lefteq = pfc.pairing(Vk, P);

    G1 temp = pfc.mult(P, inverse_h1k);
    GT righteq = pfc.pairing(Uk + temp, PKtrc);

    if (lefteq == righteq)
    {
        return true;
    }
    return false;
}

char* trace(KeyParams& params, PFC& pfc, vector<pair<G1, G1>>& PP, char* R, vector<char*> ID, vector<pair<G1, G1>>& PK, char* m1, Sigma& sigma1, char* m2, Sigma& sigma2, G1& PKtrc) {
    Big huk1 = sigma1.huk;
    pair<Big, G1> Ak1 = sigma1.Ak;
    G1 Uk1 = sigma1.U;
    G1 Vk1 = sigma1.V;
    Big huk2 = sigma2.huk;
    pair<Big, G1> Ak2 = sigma2.Ak;
    G1 Uk2 = sigma2.U;
    G1 Vk2 = sigma2.V;
    int length = ID.size();
    G1 P = params.P;
    
    char* ID1 = new char(10); 
    char* ID2 = new char(10);

    for (int i = 0; i < length; i++)
    {
        Big temp = H11(params, pfc, ID[i]) * Ak1.first;
        G1 left_temp = Ak1.second;
        G1 temp2 = pfc.mult(PP[i].second, temp);
        temp2 = -temp2;
        left_temp = left_temp + temp2;
        Big h1k = H4(params, pfc, m1, ID, PK, huk1);
        Big inverse_h1k = inverse(h1k, params.q);
        GT lefteq = pfc.pairing(PP[i].first, left_temp);
        GT righteq1 = pfc.pairing(Vk1, P);
        GT righteq2 = pfc.pairing(pfc.mult(P, inverse_h1k), PKtrc);
        GT righteq = righteq1 / righteq2;

        

        if (lefteq == righteq)
        {
            ID1 = ID[i];
            break;
        }
    }

    for (int i = 0; i < length; i++)
    {
        Big tempT = H11(params, pfc, ID[i]) * Ak2.first;
        G1 left_tempT = Ak2.second;
        G1 tempT2 = pfc.mult(PP[i].second, tempT);
        tempT2 = -tempT2;
        left_tempT = left_tempT + tempT2;
        Big h1kT = H4(params, pfc, m2, ID, PK, huk2);
        Big inverse_h1kT = inverse(h1kT, params.q);
        GT lefteqT = pfc.pairing(PP[i].first, left_tempT);
        GT righteqT1 = pfc.pairing(Vk2, P);
        GT righteqT2 = pfc.pairing(pfc.mult(P, inverse_h1kT), PKtrc);
        GT righteqT = righteqT1 / righteqT2;



        if (lefteqT == righteqT)
        {
            ID2 = ID[i];
            break;
        }
    }

    if (ID1 != ID2)
    {
        //cout << "ID1 != ID2" << endl;
        return (char*)"independent";
    }
    else
    {
        if (m1 == m2)
        {
            //cout << "m1 == m2" << endl;
            return (char*)"linked";
        }
        else
        {
            //cout << "trace success !" << endl;
            return ID1;
        }
    }
    
}

void test_trial(KeyParams& params, PFC& pfc) {
    vector<double> sign_time_list;
    vector<double> trace_time_list;
    vector<double> verify_time_list;
    vector<double> entire_time_list;
    
    Big s, SKtrc;
     
    // TRC secret and public key
    pfc.random(s);
    SKtrc = inverse(s, params.q);
    G1 PKtrc = pfc.mult(params.P, SKtrc);

    cout << "power\tsign\tverify\ttrace\tentire(ms)" << endl;

    for (int power = 0; power < 6; power++) {
        double sign_time_sum = 0;
        double trace_time_sum = 0;
        double verify_time_sum = 0;
        double entire_time_sum = 0;
        int power_of_2 = power + 1;
        int PK_num = (int)pow(2, power_of_2);
        int time_trail = 1000;

       /* vector<G1> fake_Pid(PK_num);
        vector<Big> fake_Ssk(PK_num);*/

        //pair<Big, G1> psk;
        vector<char*> ID(PK_num);
        vector<pair<G1, G1>> PP(PK_num);
        vector<G1> SK(PK_num);
        vector<pair<G1, G1>> PK(PK_num);
        char* R = (char*)"event1";

        const char* baseStr = "vehicle";
        for (int j = 0; j < PK_num; j++) {
            // 将数字转换为字符串并连接
            // 将数字转换为字符串
            std::string numStr = std::to_string(j);


            // 计算新的字符串的长度
            size_t totalLength = std::strlen(baseStr) + numStr.length() + 1;

            // 分配内存，+1 是为了包括结尾的 '\0'
            char* resultStr = new char[totalLength];

            // 复制基础字符串
            strcpy_s(resultStr, totalLength, baseStr);

            // 连接数字字符串
            strcat_s(resultStr, totalLength, numStr.c_str());

            ID[j] = resultStr;
            
        }
        
        KeyGen(params, pfc, SKtrc, ID, PP, SK, PK);

        time_t seed;
        time(&seed);
        irand((long)seed);


        for (int ii = 0; ii < time_trail; ii++) {
            clock_t start_time = clock();
            int random_position = rand(params.q) % PK_num;

            //psk = KeyGen(params, pfc);
            /*fake_Pid[random_position] = psk.second;
            Big ssk = psk.first;*/


            clock_t sign_start_time = clock();

            Sigma sigma1 = sign(params, pfc, R, ID, PK, SK[random_position], PP[random_position], random_position, (char*)"I am a girl", PKtrc);
            clock_t sign_end_time = clock();
            sign_time_sum += ((double)sign_end_time - (double)sign_start_time) / CLOCKS_PER_SEC;

            
            Sigma sigma2 = sign(params, pfc, R, ID, PK, SK[random_position], PP[random_position], random_position, (char*)"I am a boy", PKtrc);
            
            clock_t verify_start_time = clock();
            if (!singleVerify(params, pfc, R, ID, PK, (char*)"I am a girl", sigma1, PKtrc)) {
                cout << "signature verify failed" << endl;
            }
            clock_t verify_end_time = clock();
            verify_time_sum += ((double)verify_end_time - (double)verify_start_time) / CLOCKS_PER_SEC;

            clock_t trace_start_time = clock();
            char* traceID = trace(params, pfc, PP, R, ID, PK, (char*)"I am a girl", sigma1, (char*)"I am a boy", sigma2, PKtrc);
            /*if (traceID == (char*)"independent" || traceID == (char*)"linked") {
                cout << "TRC trace failed" << endl;
            }
            else
            {
                cout << "the signer's ID is " << traceID << endl;
            }*/
            //cout << traceID << endl;

            clock_t trace_end_time = clock();
            trace_time_sum += ((double)trace_end_time - (double)trace_start_time) / CLOCKS_PER_SEC;

            

            clock_t end_time = clock();
            entire_time_sum += ((double)end_time - (double)start_time) / CLOCKS_PER_SEC;
        }

        cout << power + 1 << "\t" << (sign_time_sum / time_trail) * 1000 << "\t" << (verify_time_sum / time_trail) * 1000
            << "\t" << (trace_time_sum / time_trail) * 1000 << "\t" << (entire_time_sum / time_trail) * 1000 << endl;

        sign_time_list.push_back((sign_time_sum / time_trail) * 1000);
        verify_time_list.push_back((verify_time_sum / time_trail) * 1000);
        trace_time_list.push_back((trace_time_sum / time_trail) * 1000);
        entire_time_list.push_back((entire_time_sum / time_trail) * 1000);
    }

    // Get current date
    std::time_t t = std::time(nullptr);
    std::tm now;
    localtime_s(&now, &t);

    // Format date as YYYY-MM-DD
    std::ostringstream date_stream;
    date_stream << (now.tm_year + 1900) << '-'
        << (now.tm_mon + 1) << '-'
        << now.tm_mday << '-' << now.tm_hour << '-' << now.tm_min << '-';
    std::string date_str = date_stream.str();

    // Create filename with date
    std::string filename = date_str + "CTRS Time Analysis .txt";

    // 指定文件路径
    std::string directory = "D:\\VS2019\\repo\\2024-8-6-CTRS\\test_time\\";
    //std::string filename = "output.txt";
    std::string filepath = directory + filename;

    // Writing to file
    std::ofstream text_file;
    text_file.open(filepath);

    // Writing to file
    //std::ofstream text_file(filename);
    if (!text_file.is_open()) {
        std::cerr << "Failed to open file: " << filename << std::endl;
        //return 1;
    }

    // writing to file
    //ofstream text_file("DualRing Ring Signature Time Analysis.txt");
    text_file << "2^n\tSign\tVerify\tTrace\n";
    for (size_t i = 0; i < sign_time_list.size(); i++) {
        text_file << i + 1 << "\t" << sign_time_list[i] << "\t" << verify_time_list[i] << "\t" << trace_time_list[i] << "\t" << endl;
    }
    text_file.close();
}



int main() {
    // Security level for 80 bits
    PFC pfc(80);
    //int trials = 1000;
    Big q;
    G1 P;
    pfc.random(P);

    q = pfc.order();
    // TRA secret and public key
    /*pfc.random(s);
    SKtrc = inverse(s, q);
    G1 PKtrc = pfc.mult(P, SKtrc);*/

    KeyParams params;
    params.q = q;
    params.P = P;

    test_trial(params, pfc);

    return 0;
}