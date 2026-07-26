#!/usr/bin/env python3
#
# Copyright (C) 2018-2025 Ycarus (Yannick Chabanois) <ycarus@zugaina.org> for OpenMPTCProuter
#
# This is free software, licensed under the GNU General Public License v3.0.
# See /LICENSE for more information.
#

import json
import base64
import secrets
import uuid
import configparser
import argparse
import subprocess
import os
#import sys
import glob
import socket
from operator import itemgetter
import re
import hashlib
#import pathlib
import shutil
import time
import copy
#from pprint import pprint
from datetime import datetime, timedelta
from tempfile import mkstemp
from typing import List, Optional
from shutil import move
from enum import Enum
from os import path
from ipaddress import ip_address, IPv4Address, IPv6Address
import logging
import asyncio
import fcntl
import uvicorn
import jwt
import requests
from jwt import PyJWTError
from netaddr import *
import psutil
#from netjsonconfig import OpenWrt
from fastapi import Depends, FastAPI, HTTPException, Query, Request, UploadFile
from fastapi.security import OAuth2PasswordRequestForm, OAuth2
from passlib.context import CryptContext
from fastapi.encoders import jsonable_encoder
from fastapi.security.base import SecurityBase
from fastapi.security.utils import get_authorization_scheme_param
from fastapi.openapi.docs import get_swagger_ui_html
from fastapi.openapi.models import OAuthFlows as OAuthFlowsModel
from fastapi.openapi.utils import get_openapi
from fastapi.openapi.models import SecurityBase as SecurityBaseModel
from fastapi.responses import FileResponse
from pydantic import BaseModel # pylint: disable=E0611
from starlette.status import HTTP_403_FORBIDDEN
from starlette.responses import RedirectResponse, Response, JSONResponse
#from starlette.requests import Request
import netifaces

#logging.basicConfig(filename='/tmp/omr-admin.log', encoding='utf-8', level=logging.DEBUG)
LOG = logging.getLogger('api')


logging.basicConfig(level=logging.INFO,
                    format="%(levelname)s: "
                           "%(module)s:%(funcName)s:%(lineno)d - %(message)s")
#LOG = logging.getLogger('OMR-Admin')
LOG = logging.getLogger('uvicorn.error')

PERMANENT_SESSION_LIFETIME = timedelta(hours=24)
ACCESS_TOKEN_EXPIRE_MINUTES = 1440
ALGORITHM = "HS256"
PRIMARY_ROUTER_USERNAME = "openmptcprouter"
INTERNAL_ADMIN_USERNAME = "admin"
ALLOWED_AUTH_IDENTITIES = {PRIMARY_ROUTER_USERNAME, INTERNAL_ADMIN_USERNAME}
NANBBR_AGGRESSIVENESS_MIN = 1
NANBBR_AGGRESSIVENESS_MAX = 100
NANBBR_CONFIG_FILE = '/etc/openmptcprouter-vps-admin/nanbbr-var.json'
MPTCP_LOCK_FILE = '/run/lock/omr-mptcp.lock'
NANBBR_VAR_MODULES = {
    'nanbbr1_var': 'tcp_nanbbr1_var',
    'nanbbr2_var': 'tcp_nanbbr2_var',
    'nanbbr3_var': 'tcp_nanbbr3_var',
}


def nanbbr_parameter_path(congestion_control):
    module = NANBBR_VAR_MODULES.get(congestion_control)
    if module is None:
        return None
    return '/sys/module/' + module + '/parameters/aggressiveness'


def read_nanbbr_aggressiveness():
    try:
        with open(NANBBR_CONFIG_FILE, 'r') as config_file:
            value = json.load(config_file).get('aggressiveness')
        value = int(value)
        if NANBBR_AGGRESSIVENESS_MIN <= value <= NANBBR_AGGRESSIVENESS_MAX:
            return value
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        pass
    return None


def nanbbr_capabilities():
    return {
        congestion_control: (
            path.isfile(nanbbr_parameter_path(congestion_control))
            and os.access(nanbbr_parameter_path(congestion_control), os.W_OK)
        )
        for congestion_control in NANBBR_VAR_MODULES
    }


def ensure_nanbbr_parameter(congestion_control):
    module = NANBBR_VAR_MODULES[congestion_control]
    parameter = nanbbr_parameter_path(congestion_control)
    subprocess.run(
        ['modprobe', module],
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if not path.isfile(parameter) or not os.access(parameter, os.W_OK):
        raise RuntimeError(module + ' does not expose the aggressiveness parameter')
    return parameter


def atomic_write_file(filename, content, mode=0o644):
    directory = path.dirname(filename)
    os.makedirs(directory, exist_ok=True)
    fd, tmpfile = mkstemp(dir=directory)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(content)
            output.flush()
            os.fsync(output.fileno())
        os.chmod(tmpfile, mode)
        os.replace(tmpfile, filename)
        directory_fd = os.open(directory, os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except Exception:
        try:
            os.remove(tmpfile)
        except OSError:
            pass
        raise


def nanbbr_config_content(aggressiveness):
    return (
        json.dumps(
            {'version': 1, 'aggressiveness': aggressiveness},
            sort_keys=True,
            indent=2,
        ) + '\n'
    ).encode('ascii')

# Get main net interface
FILE = open('/etc/shorewall/params.net', "r")
READ = FILE.read()
IFACE = None
for line in READ.splitlines():
    if 'NET_IFACE=' in line:
        IFACE = line.split('=', 1)[1]
FILE.close()

# Get ipv6 net interface
FILE = open('/etc/shorewall6/params.net', "r")
READ = FILE.read()
IFACE6 = None
for line in READ.splitlines():
    if 'NET_IFACE=' in line:
        IFACE6 = line.split('=', 1)[1]
FILE.close()

def delete_oldest_files(path, keep = 10):
    files = glob.glob(path)
    fileData = {}
    for fname in files:
        fileData[fname] = os.stat(fname).st_mtime
    sorted_files = sorted(fileData.items(), key = itemgetter(1))
    if len(sorted_files) > keep:
        delete = len(sorted_files) - keep
        for x in range(0, delete):
            os.remove(sorted_files[x][0])

def backup_config():
    shutil.copy2('/etc/openmptcprouter-vps-admin/omr-admin-config.json','/etc/openmptcprouter-vps-admin/omr-admin-config.json.' + str(int(time.time())))
    delete_oldest_files('/etc/openmptcprouter-vps-admin/omr-admin-config.json.*')

# Get interface rx/tx
def get_bytes(t, iface='eth0'):
    if path.exists('/sys/class/net/' + iface + '/statistics/' + t + '_bytes'):
        with open('/sys/class/net/' + iface + '/statistics/' + t + '_bytes', 'r') as f:
            data = f.read()
        return int(data)
    return 0

def get_bytes_openvpn(user):
    try:
        ovpn_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        ovpn_socket.settimeout(2)
        ovpn_socket.connect(("127.0.0.1", 65302))
        fd = ovpn_socket.makefile('rb')
        line = fd.readline()
        if not line.startswith('>INFO:OpenVPN'.encode()):
            ovpn_socket.close()
            LOG.debug("OpenVPN error")
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
        ovpn_socket.send('status\r\n'.encode())
        ovpn_stats = []
        while True:
            line = fd.readline()
            ovpn_stats.append(line.decode())
            if line.strip() == 'END'.encode():
                break
        ovpn_socket.close()
    except socket.timeout as err:
        LOG.debug("OpenVPN stats timeout (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except socket.error as err:
        LOG.debug("OpenVPN stats error (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    for data in ovpn_stats:
        if user in data:
            stats = data.split(',')
            return { 'downlinkBytes': int(stats[2]), 'uplinkBytes': int(stats[3]) }
    return { 'downlinkBytes': 0, 'uplinkBytes': 0 }


def get_bytes_ss(port):
    try:
        ss_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        ss_socket.settimeout(1)
        ss_socket.sendto('ping'.encode(), ("127.0.0.1", 8839))
        ss_recv = ss_socket.recv(1024)
    except socket.timeout as err:
        LOG.debug("Shadowsocks stats timeout (" + str(err) + ")")
        return 0
    except socket.error as err:
        LOG.debug("Shadowsocks stats error (" + str(err) + ")")
        return 0
    json_txt = ss_recv.decode("utf-8").replace('stat: ', '')
    result = json.loads(json_txt)
    if str(port) in result:
        return result[str(port)]
    return 0

def get_bytes_ss_go(user):
    try:
        #r = requests.get(url="http://127.0.0.1:65279/v1/servers/ss-2022/stats")
        r = requests.get(url="http://127.0.0.1:65279/api/ssm/v1/servers/ss-2022/stats", timeout=5)
    except requests.exceptions.Timeout:
        LOG.debug("Shadowsocks go stats timeout")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except requests.exceptions.RequestException as err:
        LOG.debug("Shadowsocks go stats error (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    try:
        if 'error' in r.json():
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except requests.exceptions.JSONDecodeError:
        try:
            r = requests.get(url="http://127.0.0.1:65279/v1/servers/ss-2022/stats", timeout=5)
            #r = requests.get(url="http://127.0.0.1:65279/api/ssm/v1/servers/ss-2022/stats")
        except requests.exceptions.Timeout:
            LOG.debug("Shadowsocks go stats timeout")
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
        except requests.exceptions.RequestException as err:
            LOG.debug("Shadowsocks go stats error (" + str(err) + ")")
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    try:
        if 'error' in r.json():
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except requests.exceptions.JSONDecodeError as err:
        LOG.debug("Shadowsocks go stats error (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    if 'users' in r.json():
        for userdata in r.json()['users']:
            if userdata['username'] == user:
                return { 'downlinkBytes': userdata['downlinkBytes'], 'uplinkBytes': userdata['uplinkBytes'] }
    return { 'downlinkBytes': 0, 'uplinkBytes': 0 }

def get_bytes_v2ray(t,user):
    if t == "tx":
        side="downlink"
    else:
        side="uplink"
    try:
        data = subprocess.check_output('/usr/bin/v2ray api stats --server=127.0.0.1:10085 -json ' + "'" + 'user>>>' + user + '>>>traffic>>>' + side + "'" + ' 2>/dev/null | jq -r .stat[0].value | tr -d " " | tr -d "\n"', shell = True)
        #data = subprocess.check_output('/usr/bin/v2ctl api --server=127.0.0.1:10085 StatsService.GetStats ' + "'" + 'name: "user>>>' + user + '>>>traffic>>>' + side + '"' + "'" + ' 2>/dev/null | grep value | cut -d: -f2 | tr -d " "', shell = True)
    except:
        return 0
    if data.decode("utf-8") != '' and data.decode("utf-8") != 'null':
        try:
            return int(data.decode("utf-8"))
        except ValueError:
            return 0
    else:
        return 0

def get_bytes_xray(t,user):
    if t == "tx":
        side="downlink"
    else:
        side="uplink"
    try:
        data = subprocess.check_output('/usr/bin/xray api stats --server=127.0.0.1:10086 -name ' + "'" + 'user>>>' + user + '>>>traffic>>>' + side + "'" + ' 2>/dev/null | jq -r .stat.value | tr -d " " | tr -d "\n"', shell = True)
    except:
        return 0
    if data.decode("utf-8") != '' and data.decode("utf-8") != 'null':
        try:
            return int(data.decode("utf-8"))
        except ValueError:
            return 0
    else:
        return 0

def get_bytes_softether(user):
    createBytesPayload = {
        "jsonrpc": "2.0",
        "id": "rpc_call_id",
        "method": "GetUser",
        "params": {
            "HubName_str": "OMRVPN",
            "Name_str": user,
        },
    }
    try:
        r = requests.post(url="http://127.0.0.1:65390/api", json=createBytesPayload, headers=softethervpnPassword, verify=False)
    except requests.exceptions.Timeout:
        LOG.debug("SoftEther VPN get bytes timeout")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except requests.exceptions.RequestException as err:
        LOG.debug("SoftEther VPN get bytes error (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    try:
        if 'error' in r.json():
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except requests.exceptions.JSONDecodeError as err:
        LOG.debug("Shadowsocks go stats error (" + str(err) + ")")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    return { 'downlinkBytes': r.json()['result']['Recv.UnicastBytes_u64'], 'uplinkBytes': r.json()['result']['Send.UnicastBytes_u64'] }

def checkIfProcessRunning(processName):
    for proc in psutil.process_iter():
        try:
            if processName.lower() in proc.name().lower():
                return True
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            pass
    return False

def file_as_bytes(file):
    with file:
        return file.read()

def check_username_serial(username, serial):
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    try:
        configdata = json.loads(content)
        data = configdata
    except ValueError as e:
        #return {'error': 'Config file not readable', 'route': 'check_serial'}
        return False
    if 'serial_enforce' not in data or data['serial_enforce'] is False:
        return True
    if 'serial' not in data['users'][0][username]:
        data['users'][0][username]['serial'] = serial
        if data:
            with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json', 'w') as outfile:
                json.dump(data, outfile, indent=4)
        return True
    if data['users'][0][username]['serial'] == serial:
        return True
    if 'serial_error' not in data['users'][0][username]:
        data['users'][0][username]['serial_error'] = 1
    else:
        data['users'][0][username]['serial_error'] = int(data['users'][0][username]['serial_error']) + 1
    backup_config()
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json', 'w') as outfile:
        json.dump(data, outfile, indent=4)
    return False

def set_global_param(key, value):
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    try:
        configdata = json.loads(content)
        data = configdata
    except ValueError as e:
        LOG.debug("Can't read file for set_global_param")
        return {'error': 'Config file not readable', 'route': 'global_param'}
    if not key in data or data[key] != value:
        data[key] = value
        #LOG.debug("backup_config() in set_global_param")
        backup_config()
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json', 'w') as outfile:
            json.dump(data, outfile, indent=4)
#    else:
#        LOG.debug("Already exist data for set_global_param key:" + key)

def modif_config_user(user, changes):
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        content = json.load(f)
    content_initial = copy.deepcopy(content)
    content['users'][0][user].update(changes)
    if content_initial != content:
        LOG.debug("backup_config() in modif_config_user")
        backup_config()
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json', 'w') as f:
            json.dump(content, f, indent=4)
    else:
        LOG.debug("No real changes in modif_config_user")

def add_ss_user(port, key, userid=0, ip=''):
    with open('/etc/shadowsocks-libev/manager.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    data = json.loads(content)
    if ip == '' and 'port_key' in data:
        if port is None or port == '' or port == 0 or port == 'None':
            port = int(max(data['port_key'], key=int)) + 1
        data['port_key'][str(port)] = key
    else:
        if 'port_conf' not in data:
            data['port_conf'] = {}
        if 'port_key' in data:
            for old_port in data['port_key']:
                data['port_conf'][old_port] = {'key': data['port_key'][old_port]}
            del data['port_key']
        if port == '' or port == "None" or port is None or port == 0:
            port = int(max(data['port_conf'], key=int)) + 1
        if ip != '':
            data['port_conf'][str(port)] = {'key': key, 'local_address': ip, 'userid': userid}
        else:
            data['port_conf'][str(port)] = {'key': key, 'userid': userid}
    with open('/etc/shadowsocks-libev/manager.json', 'w') as f:
        json.dump(data, f, indent=4)
    try:
        ss_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        if ip != '':
            data = 'add: {"server_port": ' + str(port) + ', "key": "' + key + '", "local_addr": "' + ip + '"}'
        else:
            data = 'add: {"server_port": ' + str(port) + ', "key": "' + key + '"}'
        ss_socket.settimeout(1)
        ss_socket.sendto(data.encode(), ("127.0.0.1", 8839))
    except socket.timeout as err:
        LOG.debug("Shadowsocks add timeout (" + str(err) + ")")
    except socket.error as err:
        LOG.debug("Shadowsocks add error (" + str(err) + ")")
    return port

def remove_ss_user(port):
    with open('/etc/shadowsocks-libev/manager.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    data = json.loads(content)
    if 'port_key' in data:
        if str(port) in data['port_key']:
            del data['port_key'][str(port)]
    else:
        if str(port) in data['port_conf']:
            del data['port_conf'][str(port)]
    with open('/etc/shadowsocks-libev/manager.json', 'w') as f:
        json.dump(data, f, indent=4)
    try:
        ss_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        data = 'remove: {"server_port": ' + str(port) + '}'
        ss_socket.settimeout(1)
        ss_socket.sendto(data.encode(), ("127.0.0.1", 8839))
    except socket.timeout as err:
        LOG.debug("Shadowsocks remove timeout (" + str(err) + ")")
    except socket.error as err:
        LOG.debug("Shadowsocks remove error (" + str(err) + ")")

def add_ss_go_user(user, key=''):
    try:
        r = requests.post(url="http://127.0.0.1:65279/api/ssm/v1/servers/ss-2022/users", json= {'username': user,'uPSK': key})
    except requests.exceptions.Timeout:
        LOG.debug("Shadowsocks go add timeout")
    except requests.exceptions.RequestException as err:
        try:
            r = requests.post(url="http://127.0.0.1:65279/v1/servers/ss-2022/users", json= {'username': user,'uPSK': key})
        except requests.exceptions.Timeout:
            LOG.debug("Shadowsocks go add timeout")
        except requests.exceptions.RequestException as err:
            LOG.debug("Shadowsocks go add error (" + str(err) + ")")
    return key

def remove_ss_go_user(user):
    try:
        r = requests.delete(url="http://127.0.0.1:65279/api/ssm/v1/servers/ss-2022/users/" + user)
    except requests.exceptions.Timeout:
        LOG.debug("Shadowsocks go remove timeout")
    except requests.exceptions.RequestException as err:
        try:
            r = requests.delete(url="http://127.0.0.1:65279/v1/servers/ss-2022/users/" + user)
        except requests.exceptions.Timeout:
            LOG.debug("Shadowsocks go remove timeout")
        except requests.exceptions.RequestException as err:
            LOG.debug("Shadowsocks go remove error (" + str(err) + ")")

def add_softether_user(user, password):
    createUserPayload = {
        "jsonrpc": "2.0",
        "id": "rpc_call_id",
        "method": "CreateUser",
        "params": {
            "HubName_str": "OMRVPN",
            "Name_str": user,
            "AuthType_u32": 1,
            "Auth_Password_str": password,
        },
    }
    try:
        r = requests.post(url="http://127.0.0.1:65390/api", json=createUserPayload, headers=softethervpnPassword, verify=False)
    except requests.exceptions.Timeout:
        LOG.debug("SoftEther VPN add timeout")
    except requests.exceptions.RequestException as err:
        LOG.debug("SoftEther VPN remove error (" + str(err) + ")")
    return password

def remove_softether_user(user):
    removeUserPayload = {
        "jsonrpc": "2.0",
        "id": "rpc_call_id",
        "method": "DeleteUser",
        "params": {
            "HubName_str": "OMRVPN",
            "Name_str": user,
        },
    }
    try:
        r = requests.post(url="http://127.0.0.1:65390/api", json=removeUserPayload, headers=softethervpnPassword, verify=False)
    except requests.exceptions.Timeout:
        LOG.debug("SoftEther VPN add timeout")
    except requests.exceptions.RequestException as err:
        LOG.debug("SoftEther VPN remove error (" + str(err) + ")")

def v2ray_add_user(user, v2rayuuid='', restart=1):
    if v2rayuuid == '':
        v2rayuuid = str(uuid.uuid1())
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        exist = 0
        for inbounds in data['inbounds']:
            custominbounds = {"inbounds": []}
            if inbounds['tag'] == 'omrin-tunnel':
                inbounds['settings']['clients'].append({'id': v2rayuuid, 'level': 0, 'alterId': 0, 'email': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/v2ray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("v2ray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("v2ray api adi --server=127.0.0.1:10085 /etc/v2ray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-vmess-tunnel':
                inbounds['settings']['clients'].append({'id': v2rayuuid, 'level': 0, 'alterId': 0, 'email': user})
                #os.system("v2ray api rmi --server=127.0.0.1:65080 omrin-vmess-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/v2ray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("v2ray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("v2ray api adi --server=127.0.0.1:10085 /etc/v2ray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-trojan-tunnel':
                inbounds['settings']['clients'].append({'password': v2rayuuid, 'email': user})
                #os.system("v2ray api rmi --server=127.0.0.1:65080 omrin-trojan-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/v2ray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("v2ray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("v2ray api adi --server=127.0.0.1:10085 /etc/v2ray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-socks-tunnel':
                inbounds['settings']['accounts'].append({'pass': v2rayuuid, 'user': user})
                #os.system("v2ray api rmi --server=127.0.0.1:65080 omrin-socks-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/v2ray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("v2ray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("v2ray api adi --server=127.0.0.1:10085 /etc/v2ray/newconfig.json >/dev/null 2>&1")
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        #try:
        #    data = subprocess.check_output('/usr/bin/v2ray api adi --server=127.0.0.1:10085 -users ' + "'" + '{"tag":"omrin-vmess-tunnel","users":[{"user": "' + user + '","key": "' + v2rayuuid + '"}]}' + "'", shell = True)
        #except:
        #    LOG.debug("V2Ray VMESS: Can't add user")
        if restart == 1:
            os.system("systemctl -q restart v2ray")
    return v2rayuuid

def xray_add_user(user,xrayuuid='',ukeyss2022='',restart=1, ip=''):
    if xrayuuid == '':
        xrayuuid = str(uuid.uuid1())
    if ukeyss2022 == '':
        ukeyss2022 = base64.urlsafe_b64encode(secrets.token_hex(16).encode()).decode('utf-8')
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        exist = 0
        for inbounds in data['inbounds']:
            custominbounds = {"inbounds": []}
            if inbounds['tag'] == 'omrin-tunnel':
                inbounds['settings']['clients'].append({'id': xrayuuid, 'level': 0, 'alterId': 0, 'email': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                tt = os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json 2>&1")
                LOG.debug(tt)
            if inbounds['tag'] == 'omrin-vmess-tunnel':
                inbounds['settings']['clients'].append({'id': xrayuuid, 'level': 0, 'alterId': 0, 'email': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-vmess-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                tt = os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json 2>&1")
                LOG.debug(tt)
            if inbounds['tag'] == 'omrin-trojan-tunnel':
                inbounds['settings']['clients'].append({'password': xrayuuid, 'email': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-trojan-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                tt = os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json 2>&1")
                LOG.debug(tt)
            if inbounds['tag'] == 'omrin-socks-tunnel':
                inbounds['settings']['accounts'].append({'pass': xrayuuid, 'user': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-socks-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                tt = os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json 2>&1")
                LOG.debug(tt)
            if inbounds['tag'] == 'omrin-shadowsocks-tunnel':
                inbounds['settings']['clients'].append({'password': ukeyss2022, 'email': user})
                #os.system("xray api rmi --server=127.0.0.1:65080 omrin-shadowsocks-tunnel")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                tt = os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json 2>&1")
                LOG.debug(tt)
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    if ip != '':
        try:
            xray_tag = 'output-' + str(ip)
            xray_add_routing(xray_tag,user,0)
            xray_add_outbound(xray_tag,str(ip),0)
        except Exception as exception:
            pass
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    #if initial_md5 != final_md5 and restart == 1:
    #    os.system("systemctl -q restart xray")
    return xrayuuid

def v2ray_del_user(user, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        for inbounds in data['inbounds']:
            if inbounds['tag'] == 'omrin-tunnel':
                for v2rayuser in inbounds['settings']['clients']:
                    if v2rayuser['email'] == user:
                        inbounds['settings']['clients'].remove(v2rayuser)
            if inbounds['tag'] == 'omrin-vmess-tunnel':
                for v2rayuser in inbounds['settings']['clients']:
                    if v2rayuser['email'] == user:
                        inbounds['settings']['clients'].remove(v2rayuser)
            if inbounds['tag'] == 'omrin-trojan-tunnel':
                for v2rayuser in inbounds['settings']['clients']:
                    if v2rayuser['email'] == user:
                        inbounds['settings']['clients'].remove(v2rayuser)
            if inbounds['tag'] == 'omrin-socks-tunnel':
                for v2rayuser in inbounds['settings']['accounts']:
                    if v2rayuser['user'] == user:
                        inbounds['settings']['accounts'].remove(v2rayuser)
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart v2ray")

def xray_del_user(user, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        for inbounds in data['inbounds']:
            custominbounds = {"inbounds": []}
            if inbounds['tag'] == 'omrin-tunnel':
                for xrayuser in inbounds['settings']['clients']:
                    if xrayuser['email'] == user:
                        inbounds['settings']['clients'].remove(xrayuser)
                os.system("xray api rmi --server=127.0.0.1:10086 omrin-tunnel >/dev/null 2>&1")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-vmess-tunnel':
                for xrayuser in inbounds['settings']['clients']:
                    if xrayuser['email'] == user:
                        inbounds['settings']['clients'].remove(xrayuser)
                os.system("xray api rmi --server=127.0.0.1:10086 omrin-vmess-tunnel >/dev/null 2>&1")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-trojan-tunnel':
                for xrayuser in inbounds['settings']['clients']:
                    if xrayuser['email'] == user:
                        inbounds['settings']['clients'].remove(xrayuser)
                os.system("xray api rmi --server=127.0.0.1:10086 omrin-trojan-tunnel >/dev/null 2>&1")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-socks-tunnel':
                for xrayuser in inbounds['settings']['accounts']:
                    if xrayuser['user'] == user:
                        inbounds['settings']['accounts'].remove(xrayuser)
                os.system("xray api rmi --server=127.0.0.1:10086 omrin-socks-tunnel >/dev/null 2>&1")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json >/dev/null 2>&1")
            if inbounds['tag'] == 'omrin-shadowsocks-tunnel':
                for xrayuser in inbounds['settings']['clients']:
                    if xrayuser['email'] == user:
                        inbounds['settings']['clients'].remove(xrayuser)
                os.system("xray api rmi --server=127.0.0.1:10086 omrin-shadowsocks-tunnel >/dev/null 2>&1")
                custominbounds['inbounds'].append(inbounds)
                with open('/etc/xray/newconfig.json', 'w') as f:
                    json.dump(custominbounds, f, indent=4)
                #os.system("xray api adi --server=127.0.0.1:65080 " + json.dumps(custominbounds))
                os.system("xray api adi --server=127.0.0.1:10086 /etc/xray/newconfig.json >/dev/null 2>&1")
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    #if initial_md5 != final_md5 and restart == 1:
    #    os.system("systemctl -q restart xray")

def v2ray_add_outbound(tag,ip, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        data['outbounds'].append({'protocol': 'freedom', 'settings': { 'userLevel': 0 }, 'tag': tag, 'sendThrough': ip})
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart v2ray")

def xray_add_outbound(tag,ip, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        data['outbounds'].append({'protocol': 'freedom', 'settings': { 'userLevel': 0 }, 'tag': tag, 'sendThrough': ip})
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart xray")

def v2ray_del_outbound(tag, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        for outbounds in data['outbounds']:
            if outbounds['tag'] == tag:
                data['outbounds'].remove(outbounds)
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart v2ray")

def xray_del_outbound(tag, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        for outbounds in data['outbounds']:
            if outbounds['tag'] == tag:
                data['outbounds'].remove(outbounds)
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart xray")

def v2ray_add_routing(tag, user, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        if user == "":
                data['routing']['rules'].append({'type': 'field', 'inboundTag': ( 'omrin-tunnel' ), 'outboundTag': tag})
        else:
                data['routing']['rules'].append({'type': 'field', 'inboundTag': ( 'omrin-tunnel' ), 'user': ( user ), 'outboundTag': tag})

    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart v2ray")

def xray_add_routing(tag, user, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        if user == "":
                data['routing']['rules'].insert(0,{'type': 'field', 'inboundTag': ( 'omrin-tunnel' ), 'outboundTag': tag})
        else:
                data['routing']['rules'].insert(0,{'type': 'field', 'inboundTag': ( 'omrin-tunnel' ), 'user': ( user ), 'outboundTag': tag})
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart xray")

def v2ray_del_routing(tag, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        for rules in data['routing']['rules']:
            if rules['outboundTag'] == tag:
                data['routing']['rules'].remove(rules)
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart v2ray")

def xray_del_routing(tag, restart=1):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        for rules in data['routing']['rules']:
            if rules['outboundTag'] == tag:
                data['routing']['rules'].remove(rules)
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5 and restart == 1:
        os.system("systemctl -q restart xray")


def add_gre_tunnels(addtouser = 'openmptcprouter', addwithip = ''):
    LOG.debug("Add gre-tunnels now...")
    nbip = 0
    allips = []
    for intf in netifaces.interfaces():
        addrs = netifaces.ifaddresses(intf)
        try:
            ipv4_addr_list = addrs[netifaces.AF_INET]
            for ip_info in ipv4_addr_list:
                addr = ip_info['addr']
                #LOG.debug("Check if " + str(addr) + " is not IPv4 or reserved")
                if not IPAddress(addr).is_link_local() and not IPAddress(addr).is_reserved() and not IPAddress(addr).is_private():
                    allips.append(addr)
                    nbip = nbip + 1
        except Exception as exception:
            #LOG.debug("There is an exception in add_gre_tunnels")
            pass

    if nbip > 1:
        nbgre = 0
        nbip = 0
        initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/snat', 'rb'))).hexdigest()
        for intf in netifaces.interfaces():
            addrs = netifaces.ifaddresses(intf)
            try:
                ipv4_addr_list = addrs[netifaces.AF_INET]
                for ip_info in ipv4_addr_list:
                    addr = ip_info['addr']
                    if not IPAddress(addr).is_private() and not IPAddress(addr).is_reserved() and not IPAddress(addr).is_link_local():
                        netmask = ip_info['netmask']
                        ip = IPNetwork('10.255.250.0/24')
                        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
                            content = json.load(f)
                        for user in content['users'][0]:
                            if user != "admin" and ((user == addtouser and str(ip) == addwithip) or user == 'openmptcprouter'):
                                subnets = ip.subnet(30)
                                network = list(subnets)[nbgre]
                                nbgre = nbgre + 1
                                userid = 0
                                username = user
                                iface = intf.split(':')[0]
                                if 'userid' in content['users'][0][user]:
                                    userid = content['users'][0][user]['userid']
                                if 'username' in content['users'][0][user]:
                                    username = content['users'][0][user]['username']
                                gre_intf = 'gre-user' + str(userid) + '-ip' + str(nbip)
                                if not os.path.isfile('/etc/openmptcprouter-vps-admin/intf/' + gre_intf):
                                    with open('/etc/openmptcprouter-vps-admin/intf/' + gre_intf, 'w') as n:
                                        n.write('INTF=' + str(intf.split(':')[0]) + "\n")
                                        n.write('INTFADDR=' + str(addr) + "\n")
                                        n.write('INTFNETMASK=' + str(netmask) + "\n")
                                        n.write('NETWORK=' + str(network) + "\n")
                                        n.write('LOCALIP=' + str(list(network)[1]) + "\n")
                                        n.write('REMOTEIP=' + str(list(network)[2]) + "\n")
                                        n.write('NETMASK=255.255.255.252' + "\n")
                                        n.write('BROADCASTIP=' + str(network.broadcast) + "\n")
                                        n.write('USERNAME=' + str(username) + "\n")
                                        n.write('USERID=' + str(userid) + "\n")
                                fd, tmpfile = mkstemp()
                                with open('/etc/shorewall/snat', 'r') as h, open(tmpfile, 'a+') as n:
                                    for line in h:
                                        if not '# OMR GRE for public IP ' + str(addr) + ' for user ' + str(user) in line:
                                            n.write(line)
                                    n.write('SNAT(' + str(addr) + ')	' + str(network) + '	' + str(iface) + ' # OMR GRE for public IP ' + str(addr) + ' for user ' + str(user) + "\n")
                                    n.write('SNAT(' + str(list(network)[1]) + ')	-	' + gre_intf + ' # OMR GRE for public IP ' + str(addr) + ' for user ' + str(user) + "\n")
                                os.close(fd)
                                move(tmpfile, '/etc/shorewall/snat')
                                    #fd, tmpfile = mkstemp()
                                    #with open('/etc/shorewall/interfaces', 'r') as h, open(tmpfile, 'a+') as n:
                                    #    for line in h:
                                    #        if not 'gre-user' + str(userid) + '-ip' + str(nbip) in line:
                                    #            n.write(line)
                                    #    n.write('vpn	gre-user' + str(userid) + '-ip' + str(nbip) + '	nosmurfs,tcpflags' + "\n")
                                    #os.close(fd)
                                    #move(tmpfile, '/etc/shorewall/interfaces')
                                if str(iface) != IFACE:
                                    fd, tmpfile = mkstemp()
                                    with open('/etc/shorewall/interfaces', 'r') as h, open(tmpfile, 'a+') as n:
                                        for line in h:
                                            if not str(iface) in line:
                                                n.write(line)
                                        n.write('net	' + str(iface) + '	dhcp,nosmurfs,tcpflags,routefilter,sourceroute=0' + "\n")
                                    os.close(fd)
                                    move(tmpfile, '/etc/shorewall/interfaces')
                                user_gre_tunnels = {}
                                if 'gre_tunnels' in content['users'][0][user]:
                                    user_gre_tunnels = content['users'][0][user]['gre_tunnels']
                                user_gre_tunnels[gre_intf] = {'local_ip': str(list(network)[1]), 'remote_ip': str(list(network)[2]), 'public_ip': str(addr)}
                                if os.path.isfile('/etc/shadowsocks-libev/manager.json') and not 'shadowsocks_port' in user_gre_tunnels[gre_intf]:
                                    with open('/etc/shadowsocks-libev/manager.json') as g:
                                        contentss = g.read()
                                    contentss = re.sub(r",\s*}", "}", contentss) # pylint: disable=W1401
                                    datass = json.loads(contentss)
                                    makechange = True
                                    shadowsocks_port = 65101
                                    if 'port_conf' in datass:
                                        for sscport in datass['port_conf']:
                                            if 'local_address' in datass['port_conf'][sscport] and datass['port_conf'][sscport]['local_address'] == str(addr):
                                                shadowsocks_port = sscport
                                                makechange = False
                                    if makechange:
                                        ss_port = content['users'][0][user]['shadowsocks_port']
                                        if 'port_key' in datass:
                                            ss_key = datass['port_key'][str(ss_port)]
                                        if 'port_conf' in datass:
                                            ss_key = datass['port_conf'][str(ss_port)]['key']
                                        if gre_intf not in user_gre_tunnels:
                                            user_gre_tunnels[gre_intf] = {}
                                        shadowsocks_port = str(add_ss_user('', ss_key, userid, str(addr))) # pylint: disable=E0606
                                        user_gre_tunnels[gre_intf].update({'shadowsocks_port': shadowsocks_port})
                                        #user_gre_tunnels[gre_intf] = {'local_ip': str(list(network)[1]), 'remote_ip': str(list(network)[2]), 'public_ip': str(addr)}
                                        #modif_config_user(user, {'gre_tunnels': user_gre_tunnels})
                                if os.path.isfile('/etc/xray/xray-server.json') and not 'xray' in user_gre_tunnels[gre_intf]:
                                    try:
                                        xray_user = str(username) + gre_intf
                                        xrayuuid = str(uuid.uuid1())
                                        ukeyss2022 = base64.urlsafe_b64encode(secrets.token_hex(16).encode()).decode('utf-8')
                                        LOG.debug("Delete XRay user...")
                                        xray_del_user(xray_user)
                                        LOG.debug("Create XRay user...")
                                        xray_add_user(xray_user,xrayuuid,ukeyss2022)
                                        xray_tag = 'output-' + str(addr)
                                        LOG.debug("Delete XRay routing...")
                                        xray_del_routing(xray_tag)
                                        LOG.debug("Add XRay routing...")
                                        xray_add_routing(xray_tag,xray_user,0)
                                        LOG.debug("Delete XRay outbound...")
                                        xray_del_outbound(xray_tag)
                                        LOG.debug("Add XRay outbound...")
                                        xray_add_outbound(xray_tag,str(addr),0)
                                        if gre_intf not in user_gre_tunnels:
                                            user_gre_tunnels[gre_intf] = {}
                                        LOG.debug("Prepare json XRay outbound...")
                                        user_gre_tunnels[gre_intf].update({'xray': {'uuid': xrayuuid,'ss2022': ukeyss2022}})
                                    except Exception as exception:
                                        pass
                                modif_config_user(user, {'gre_tunnels': user_gre_tunnels})
                        nbip = nbip + 1
            except Exception as exception:
                pass
        final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/snat', 'rb'))).hexdigest()
        if initial_md5 != final_md5:
            os.system("systemctl -q reload shorewall")
            if os.path.isfile('/etc/shadowsocks-libev/manager.json'):
                os.system("systemctl -q restart shadowsocks-libev-manager@manager")
    set_global_param('allips', allips)

def add_glorytun_tcp(userid):
    port = '650{:02d}'.format(userid)
    ip = IPNetwork('10.255.255.0/24')
    subnets = ip.subnet(30)
    network = list(subnets)[userid]
    with open('/etc/glorytun-tcp/tun0', 'r') as f, \
          open('/etc/glorytun-tcp/tun' + str(userid), 'w') as n:
        for line in f:
            if 'PORT' in line:
                n.write('PORT=' + port + "\n")
            elif 'DEV' in line:
                n.write('DEV=tun' + str(userid) + "\n")
            elif (not 'LOCALIP' in line
                  and not 'REMOTEIP' in line
                  and not 'BROADCASTIP' in line
                  and not line == "\n"):
                n.write(line)
        n.write("\n" + 'LOCALIP=' + str(list(network)[1]) + "\n")
        n.write('REMOTEIP=' + str(list(network)[2]) + "\n")
        n.write('BROADCASTIP=' + str(network.broadcast) + "\n")
    glorytun_tcp_key = secrets.token_hex(32)
    with open('/etc/glorytun-tcp/tun' + str(userid) + '.key', 'w') as f:
        f.write(glorytun_tcp_key.upper())
    os.system("systemctl -q enable glorytun-tcp@tun" + str(userid))
    os.system("systemctl -q restart glorytun-tcp@tun" + str(userid))

def remove_glorytun_tcp(userid):
    os.system("systemctl -q disable glorytun-tcp@tun" + str(userid))
    os.system("systemctl -q stop glorytun-tcp@tun" + str(userid))
    os.remove('/etc/glorytun-tcp/tun' + str(userid) + '.key')

def add_glorytun_udp(userid):
    port = '650{:02d}'.format(userid)
    ip = IPNetwork('10.255.254.0/24')
    subnets = ip.subnet(30)
    network = list(subnets)[userid]
    with open('/etc/glorytun-udp/tun0', 'r') as f, \
          open('/etc/glorytun-udp/tun' + str(userid), 'w') as n:
        for line in f:
            if 'BIND_PORT' in line:
                n.write('BIND_PORT=' + port + "\n")
            elif 'DEV' in line:
                n.write('DEV=tun' + str(userid) + "\n")
            elif (not 'LOCALIP' in line
                  and not 'REMOTEIP' in line
                  and not 'BROADCASTIP' in line
                  and not line == "\n"):
                n.write(line)
        n.write("\n" + 'LOCALIP=' + str(list(network)[1]) + "\n")
        n.write('REMOTEIP=' + str(list(network)[2]) + "\n")
        n.write('BROADCASTIP=' + str(network.broadcast) + "\n")
    with open('/etc/glorytun-tcp/tun' + str(userid) + '.key', 'r') as f, \
          open('/etc/glorytun-udp/tun' + str(userid) + '.key', 'w') as n:
        for line in f:
            n.write(line)
    os.system("systemctl -q enable glorytun-udp@tun" + str(userid))
    os.system("systemctl -q restart glorytun-udp@tun" + str(userid))

def remove_glorytun_udp(userid):
    os.system("systemctl -q disable glorytun-udp@tun" + str(userid))
    os.system("systemctl -q stop glorytun-udp@tun" + str(userid))
    os.remove('/etc/glorytun-udp/tun' + str(userid) + '.key')
    os.remove('/etc/glorytun-udp/tun' + str(userid))


def add_dsvpn(userid):
    port = '654{:02d}'.format(userid)
    ip = IPNetwork('10.255.251.0/24')
    subnets = ip.subnet(30)
    network = list(subnets)[userid]
    with open('/etc/dsvpn/dsvpn0', 'r') as f, open('/etc/dsvpn/dsvpn' + str(userid), 'w') as n:
        for line in f:
            if 'PORT' in line:
                n.write('PORT=' + port + "\n")
            elif 'DEV' in line:
                n.write('DEV=dsvpn' + str(userid) + "\n")
            elif 'LOCALTUNIP' in line:
                n.write('LOCALTUNIP=' + str(list(network)[1]) + "\n")
            elif 'REMOTETUNIP' in line:
                n.write('REMOTETUNIP=' + str(list(network)[2]) + "\n")
            else:
                n.write(line)
    dsvpn_key = secrets.token_hex(32)
    with open('/etc/dsvpn/dsvpn' + str(userid) + '.key', 'w') as f:
        f.write(dsvpn_key.upper())
    os.system("systemctl -q restart dsvpn-server@dsvpn" + str(userid))
    os.system("systemctl -q enable dsvpn-server@dsvpn" + str(userid))
def remove_dsvpn(userid):
    os.system("systemctl -q disable dsvpn-server@dsvpn" + str(userid))
    os.system("systemctl -q stop dsvpn-server@dsvpn" + str(userid))
    os.remove('/etc/dsvpn/dsvpn' + str(userid))
    os.remove('/etc/dsvpn/dsvpn' + str(userid) + '.key')


def ordered(obj):
    if isinstance(obj, dict):
        return sorted((k, ordered(v)) for k, v in obj.items())
    if isinstance(obj, list):
        return sorted(ordered(x) for x in obj)
    else:
        return obj

def v2ray_add_port(user, port, proto, name, destip, destport):
    userid = user.userid
    if userid is None:
        userid = 0
    tag = user.username + '_redir_' + proto + '_' + str(port) + '_to_' + destip + ':' + str(destport)
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        exist = 0
        for inbounds in data['inbounds']:
            LOG.debug(inbounds)
            if inbounds['tag'] == tag:
                exist = 1
        if exist == 0:
            inbounds = {'tag': tag, 'port': int(port), 'protocol': 'dokodemo-door', 'settings': {'network': proto, 'port': int(destport), 'address': destip}}
            #inbounds = {'tag': user.username + '_redir_' + proto + '_' + str(port), 'port': str(port), 'protocol': 'dokodemo-door', 'settings': {'network': proto, 'port': str(destport), 'address': destip}}
            data['inbounds'].append(inbounds)
            routing = {'type': 'field','inboundTag': [tag], 'outboundTag': 'OMRLan'}
            data['routing']['rules'].append(routing)
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart v2ray")

def xray_add_port(user, port, proto, name, destip, destport):
    userid = user.userid
    if userid is None:
        userid = 0
    tag = user.username + '_redir_' + proto + '_' + str(port) + '_to_' + destip + ':' + str(destport)
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        exist = 0
        for inbounds in data['inbounds']:
            LOG.debug(inbounds)
            if inbounds['tag'] == tag:
                exist = 1
        if exist == 0:
            inbounds = {'tag': tag, 'port': int(port), 'protocol': 'dokodemo-door', 'settings': {'network': proto, 'port': int(destport), 'address': destip}}
            #inbounds = {'tag': user.username + '_redir_' + proto + '_' + str(port), 'port': str(port), 'protocol': 'dokodemo-door', 'settings': {'network': proto, 'port': str(destport), 'address': destip}}
            data['inbounds'].append(inbounds)
            routing = {'type': 'field','inboundTag': [tag], 'outboundTag': 'direct'}
            data['routing']['rules'].append(routing)
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart xray")


XRAY_RPF_REVERSE_PORT = 65443

def xray_rpf_safe(value):
    return re.sub(r'[^A-Za-z0-9_.-]', '_', str(value))

def xray_rpf_user_uuid(user):
    username = user.username
    try:
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
            omr_config_data = json.load(f)
        return omr_config_data['users'][0][username]['xray']['key']
    except Exception:
        return os.popen("jq -r '.inbounds[0].settings.clients[] | select(.email==" + '"' + username + '"' + ") | .id' /etc/xray/xray-server.json").read().rstrip()

def xray_write_config_if_valid(data, initial_md5):
    fd, tmpfile = mkstemp(suffix='.json')
    with os.fdopen(fd, 'w') as f:
        json.dump(data, f, indent=4)
    if subprocess.call(['xray', 'run', '-test', '-config', tmpfile], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0:
        os.remove(tmpfile)
        return {'result': 'error', 'reason': 'XRay generated config is invalid'}
    os.chmod(tmpfile, 0o644)
    move(tmpfile, '/etc/xray/xray-server.json')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart xray")
    return {'result': 'done', 'reason': 'changes applied'}

def xray_rpf_add_port(user, port, proto, name, destip, destport):
    if not str(port).isdigit() or not str(destport).isdigit():
        return {'result': 'error', 'reason': 'XRay reverse port forwarding supports one TCP port per rule only'}
    if proto != 'tcp':
        return {'result': 'error', 'reason': 'XRay reverse port forwarding supports TCP only'}
    if destip == '' or destport == '':
        return {'result': 'error', 'reason': 'Destination IP and port are required'}
    xrayuuid = xray_rpf_user_uuid(user)
    if xrayuuid == '' or xrayuuid == 'null':
        return {'result': 'error', 'reason': 'XRay user UUID not found'}

    shorewall_add_port(user, str(XRAY_RPF_REVERSE_PORT), 'tcp', 'xray rpf reverse')

    username = user.username
    safe_username = xray_rpf_safe(username)
    reverse_tag = 'omr-rpf-reverse-' + safe_username
    listener_tag = 'omr-rpf-reverse-listen'
    public_tag = 'omr-rpf-' + safe_username + '-' + proto + '-' + str(port)
    legacy_tag = username + '_redir_' + proto + '_' + str(port) + '_to_' + destip + ':' + str(destport)
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()

    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)

    data.setdefault('inbounds', [])
    data.setdefault('routing', {})
    data['routing'].setdefault('rules', [])

    listener = None
    for inbound in data['inbounds']:
        if inbound.get('tag') == listener_tag:
            listener = inbound
            break
    if listener is None:
        listener = {
            'tag': listener_tag,
            'listen': '0.0.0.0',
            'port': XRAY_RPF_REVERSE_PORT,
            'protocol': 'vless',
            'settings': {'decryption': 'none', 'clients': []},
            'streamSettings': {'network': 'tcp', 'sockopt': {'tcpMptcp': True, 'mark': 0}}
        }
        data['inbounds'].append(listener)
    listener['listen'] = '0.0.0.0'
    listener['port'] = XRAY_RPF_REVERSE_PORT
    listener['protocol'] = 'vless'
    listener.setdefault('settings', {})
    listener['settings']['decryption'] = 'none'
    listener['settings'].setdefault('clients', [])
    listener['streamSettings'] = {'network': 'tcp', 'sockopt': {'tcpMptcp': True, 'mark': 0}}
    listener['settings']['clients'] = [
        c for c in listener['settings']['clients']
        if c.get('email') != username and c.get('id') != xrayuuid
    ]
    listener['settings']['clients'].append({
        'id': xrayuuid,
        'email': username,
        'reverse': {'tag': reverse_tag}
    })

    remove_tags = [public_tag, legacy_tag]
    data['inbounds'] = [i for i in data['inbounds'] if i.get('tag') not in remove_tags]
    data['routing']['rules'] = [
        r for r in data['routing']['rules']
        if not any(t in r.get('inboundTag', []) for t in remove_tags)
    ]

    data['inbounds'].append({
        'tag': public_tag,
        'listen': '0.0.0.0',
        'port': int(port),
        'protocol': 'tunnel',
        'settings': {
            'allowedNetwork': 'tcp',
            'portMap': {str(port): destip + ':' + str(destport)}
        },
        'streamSettings': {'network': 'tcp'}
    })
    data['routing']['rules'].append({
        'type': 'field',
        'inboundTag': [public_tag],
        'outboundTag': reverse_tag
    })

    return xray_write_config_if_valid(data, initial_md5)

def xray_rpf_del_port(user, port, proto, name, destip, destport):
    username = user.username
    safe_username = xray_rpf_safe(user.username)
    public_tag = 'omr-rpf-' + safe_username + '-' + proto + '-' + str(port)
    listener_tag = 'omr-rpf-reverse-listen'
    remove_reverse_port = False
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
    data['inbounds'] = [i for i in data.get('inbounds', []) if i.get('tag') != public_tag]
    data.setdefault('routing', {})
    data['routing'].setdefault('rules', [])
    data['routing']['rules'] = [
        r for r in data['routing']['rules']
        if public_tag not in r.get('inboundTag', [])
    ]

    user_has_public_rpf = any(
        i.get('tag', '').startswith('omr-rpf-' + safe_username + '-')
        for i in data.get('inbounds', [])
    )
    if not user_has_public_rpf:
        xrayuuid = xray_rpf_user_uuid(user)
        for inbound in list(data.get('inbounds', [])):
            if inbound.get('tag') != listener_tag:
                continue
            clients = inbound.get('settings', {}).get('clients', [])
            inbound['settings']['clients'] = [
                c for c in clients
                if c.get('email') != username and c.get('id') != xrayuuid
            ]
            if len(inbound['settings']['clients']) == 0:
                data['inbounds'] = [i for i in data['inbounds'] if i.get('tag') != listener_tag]

    any_public_rpf = any(
        i.get('tag', '').startswith('omr-rpf-') and i.get('tag') != listener_tag
        for i in data.get('inbounds', [])
    )
    remove_reverse_port = not any_public_rpf
    result = xray_write_config_if_valid(data, initial_md5)
    if result.get('result') == 'done' and remove_reverse_port:
        shorewall_del_port(username, str(XRAY_RPF_REVERSE_PORT), 'tcp', 'xray rpf reverse')
    return result


def v2ray_del_port(user, port, proto, name, destip, destport):
    userid = user.userid
    if userid is None:
        userid = 0
    tag = user.username + '_redir_' + proto + '_' + str(port)
    if destip != '':
        tag = tag + '_to_' + destip + ':' + str(destport)
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    with open('/etc/v2ray/v2ray-server.json') as f:
        data = json.load(f)
        for inbounds in data['inbounds']:
            if inbounds['tag'] == tag:
                data['inbounds'].remove(inbounds)
        for routing in data['routing']['rules']:
            if routing['inboundTag'][0] == tag:
                data['routing']['rules'].remove(routing)
    with open('/etc/v2ray/v2ray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart v2ray")

def xray_del_port(user, port, proto, name, destip, destport):
    userid = user.userid
    if userid is None:
        userid = 0
    tag = user.username + '_redir_' + proto + '_' + str(port)
    if destip != '':
        tag = tag + '_to_' + destip + ':' + str(destport)
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    with open('/etc/xray/xray-server.json') as f:
        data = json.load(f)
        for inbounds in data['inbounds']:
            if inbounds['tag'] == tag:
                data['inbounds'].remove(inbounds)
        for routing in data['routing']['rules']:
            if routing['inboundTag'][0] == tag:
                data['routing']['rules'].remove(routing)
    with open('/etc/xray/xray-server.json', 'w') as f:
        json.dump(data, f, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart xray")

def shorewall_add_port(user, port, proto, name, fwtype='ACCEPT', source_dip='', dest_ip='', vpn='default', gencomment='', dest_port=''):
    userid = user.userid
    if userid is None:
        userid = 0
    dnat_port = ':' + str(dest_port) if fwtype == 'DNAT' and dest_port not in ('', None) else ''
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/shorewall/rules', 'r') as f, \
          open(tmpfile, 'a+') as n:
        for line in f:
            if source_dip == '' and dest_ip == '':
                if (fwtype == 'ACCEPT' and not port + '	# OMR open ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + gencomment in line):
                    n.write(line)
                elif fwtype == 'DNAT' and not port + '	# OMR redirect ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment in line:
                    n.write(line)
            else:
                comment = ''
                if source_dip != '':
                    comment = ' to ' + source_dip
                if dest_ip != '':
                    comment = comment + ' from ' + dest_ip
                if (fwtype == 'ACCEPT' and not '# OMR ' + user.username + ' open ' + name + ' port ' + proto + comment + gencomment in line):
                    n.write(line)
                elif fwtype == 'DNAT' and not '# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
        if source_dip == '' and dest_ip == '':
            if fwtype == 'ACCEPT':
                n.write('ACCEPT		net		$FW		' + proto + '	' + port + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + gencomment + "\n")
            elif fwtype == 'DNAT' and userid == 0:
                n.write('DNAT		net		vpn:$OMR_ADDR' + dnat_port + '	' + proto + '	' + port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment + "\n")
            elif fwtype == 'DNAT' and userid != 0:
                n.write('DNAT		net		vpn:$OMR_ADDR_USER' + str(userid) + dnat_port + '	' + proto + '	' + port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment + "\n")
        else:
            net = 'net'
            comment = ''
            if source_dip != '':
                comment = ' to ' + source_dip
            if dest_ip != '':
                comment = comment + ' from ' + dest_ip
                net = 'net:' + dest_ip
            if fwtype == 'ACCEPT':
                n.write('ACCEPT		' + net + '		$FW		' + proto + '	' + port + '	-	' + source_dip + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + comment + gencomment + "\n")
            elif fwtype == 'DNAT' and vpn != 'default':
                n.write('DNAT		' + net + '		vpn:' + vpn + dnat_port + '	' + proto + '	' + port + '	-	' + source_dip +  '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment +  gencomment + "\n")
                #n.write('DNAT		' + net + '		vpn:$OMR_ADDR' + '	' + proto + '	' + port + '	-	' + source_dip +  '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment +  "\n")
            elif fwtype == 'DNAT' and userid == 0:
                n.write('DNAT		' + net + '		vpn:$OMR_ADDR' + dnat_port + '	' + proto + '	' + port + '	-	' + source_dip + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment + "\n")
            elif fwtype == 'DNAT' and userid != 0:
                n.write('DNAT		' + net + '		vpn:$OMR_ADDR_USER' + str(userid) + dnat_port + '	' + proto + '	' + port + '	-	' + source_dip + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment + "\n")
    os.close(fd)
    move(tmpfile, '/etc/shorewall/rules')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall")

def shorewall_del_port(username, port, proto, name, fwtype='ACCEPT', source_dip='', dest_ip='', gencomment=''):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/shorewall/rules', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if source_dip == '' and dest_ip == '':
                if fwtype == 'ACCEPT' and not port + '	# OMR open ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + username + ' open ' + name + ' port ' + proto + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not port + '	# OMR redirect ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + username + ' redirect ' + name + ' port ' + proto + gencomment  in line:
                    n.write(line)
            else:
                comment = ''
                if source_dip != '':
                    comment = ' to ' + source_dip
                if dest_ip != '':
                    comment = comment + ' from ' + dest_ip
                if fwtype == 'ACCEPT' and not '# OMR ' + username + ' open ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not '# OMR ' + username + ' redirect ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/shorewall/rules')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall")

def shorewall6_add_port(user, port, proto, name, fwtype='ACCEPT', source_dip='', dest_ip='', gencomment='', dest_port=''):
    userid = user.userid
    if userid is None:
        userid = 0
    vpn = 'default'
    dnat_port = ':' + str(dest_port) if fwtype == 'DNAT' and dest_port not in ('', None) else ''
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/shorewall6/rules', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if source_dip == '' and dest_ip == '':
                if fwtype == 'ACCEPT' and not port + '	# OMR open ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not port + '	# OMR redirect ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment in line:
                    n.write(line)
            else:
                comment = ''
                if source_dip != '':
                    comment = ' to ' + source_dip
                if dest_ip != '':
                    comment = comment + ' from ' + dest_ip
                if fwtype == 'ACCEPT' and not '# OMR ' + user.username + ' open ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not '# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
        if source_dip == '' and dest_ip == '':
            if fwtype == 'ACCEPT':
                n.write('ACCEPT		net		$FW		' + proto + '	' + port + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + gencomment + "\n")
            elif fwtype == 'DNAT' and userid == 0:
                n.write('DNAT		net		vpn:$OMR_ADDR' + dnat_port + '	' + proto + '	' + port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment + "\n")
            elif fwtype == 'DNAT' and userid != 0:
                n.write('DNAT		net		vpn:$OMR_ADDR_USER' + str(userid) + dnat_port + '	' + proto + '	' + port + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + gencomment + "\n")
        else:
            net = 'net'
            comment = ''
            if source_dip != '':
                comment = ' to ' + source_dip
            if dest_ip != '':
                comment = comment + ' from ' + dest_ip
                net = 'net:' + dest_ip
            if fwtype == 'ACCEPT':
                n.write('ACCEPT		' + net + '		$FW		' + proto + '	' + port +  '	-	' + source_dip + '	# OMR ' + user.username + ' open ' + name + ' port ' + proto + comment + gencomment + "\n")
            elif fwtype == 'DNAT' and vpn != 'default':
                n.write('DNAT		' + net + '		vpn:' + vpn + dnat_port + '	' + proto + '	' + port + '	-	' + source_dip +  '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment +  gencomment + "\n")
            elif fwtype == 'DNAT' and userid == 0:
                n.write('DNAT		' + net + '		vpn:$OMR_ADDR' + dnat_port + '	' + proto + '	' + port +  '	-	' + source_dip + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment + "\n")
            elif fwtype == 'DNAT' and userid != 0:
                n.write('DNAT		' + net + '		vpn:$OMR_ADDR_USER' + str(userid) + dnat_port + '	' + proto + '	' + port +  '	-	' + source_dip + '	# OMR ' + user.username + ' redirect ' + name + ' port ' + proto + comment + gencomment + "\n")
    os.close(fd)
    move(tmpfile, '/etc/shorewall6/rules')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall6")

def shorewall6_del_port(username, port, proto, name, fwtype='ACCEPT', source_dip='', dest_ip='', gencomment=''):
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/shorewall6/rules', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if source_dip == '' and dest_ip == '':
                if fwtype == 'ACCEPT' and not port + '	# OMR open ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + username + ' open ' + name + ' port ' + proto + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not port + '	# OMR redirect ' + name + ' port ' + proto + gencomment in line and not port + '	# OMR ' + username + ' redirect ' + name + ' port ' + proto + gencomment  in line:
                    n.write(line)
            else:
                comment = ''
                if source_dip != '':
                    comment = ' to ' + source_dip
                if dest_ip != '':
                    comment = comment + ' from ' + dest_ip
                if fwtype == 'ACCEPT' and not '# OMR ' + username + ' open ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
                elif fwtype == 'DNAT' and not '# OMR ' + username + ' redirect ' + name + ' port ' + proto + comment + gencomment in line:
                    n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/shorewall6/rules')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall6")

def set_lastchange(sync=0):
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    try:
        configdata = json.loads(content)
        data = configdata
    except ValueError as e:
        return {'error': 'Config file not readable', 'route': 'lastchange'}
    data["lastchange"] = time.time() + sync
    if data and data != configdata:
        LOG.debug("backup_config() in set_last_change")
        backup_config()
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json', 'w') as outfile:
            json.dump(data, outfile, indent=4)
    else:
        LOG.debug("Empty data for set_last_change")


with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
    omr_config_data = json.load(f)
if 'debug' in omr_config_data and omr_config_data['debug']:
    LOG.setLevel(logging.DEBUG)
if not 'gre_tunnels' in omr_config_data or omr_config_data['gre_tunnels']:
    LOG.debug("Add GRE tunnels")
    add_gre_tunnels()

fake_users_db = omr_config_data['users'][0]

# Generate a random secret key
if 'secret_key' in omr_config_data:
    SECRET_KEY = omr_config_data['secret_key']
else:
    SECRET_KEY = uuid.uuid4().hex
    set_global_param('secret_key',SECRET_KEY)

if 'softethervpn_admin_password' in omr_config_data:
    softethervpnPassword = { "X-VPNADMIN-PASSWORD": omr_config_data['softethervpn_admin_password'] }


def verify_password(plain_password, user_password):
    if secrets.compare_digest(plain_password,user_password):
        LOG.debug("password true")
        return True
    return False

def get_password_hash(password):
    return password

def get_user(db, username: str):
    if username in db:
        user_dict = db[username]
        return UserInDB(**user_dict)

def get_primary_router_user():
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        omr_config_data = json.load(f)
    router_user = get_user(omr_config_data['users'][0], PRIMARY_ROUTER_USERNAME)
    if router_user is None:
        raise HTTPException(status_code=500, detail="Primary router user not configured")
    return router_user

def authenticate_user(fake_db, username: str, password: str):
    if username not in ALLOWED_AUTH_IDENTITIES:
        LOG.debug("unsupported authentication identity")
        return False
    user = get_user(fake_db, username)
    if not user:
        LOG.debug("user doesn't exist")
        return False
    if not verify_password(password, user.user_password):
        LOG.debug("wrong password")
        return False
    return user

class Token(BaseModel):
    access_token: str = None
    token_type: str = None


class TokenData(BaseModel):
    username: str = None

class User(BaseModel):
    username: str
    vpn: str = None
    vpn_port: int = None
    vpn_client_ip: str = None
    permissions: str = 'rw'
    shadowsocks_port: int = None
    disabled: bool = 'false'
    userid: int = None


class UserInDB(User):
    user_password: str

# Add support for auth before seeing doc
class OAuth2PasswordBearerCookie(OAuth2):
    def __init__(
            self,
            tokenUrl: str,
            scheme_name: str = None,
            scopes: dict = None,
            auto_error: bool = True,
    ):
        if not scopes:
            scopes = {}
        flows = OAuthFlowsModel(password={"tokenUrl": tokenUrl, "scopes": scopes})
        super().__init__(flows=flows, scheme_name=scheme_name, auto_error=auto_error)

    async def __call__(self, request: Request) -> Optional[str]:
        header_authorization: str = request.headers.get("Authorization")
        cookie_authorization: str = request.cookies.get("Authorization")

        header_scheme, header_param = get_authorization_scheme_param(
            header_authorization
        )
        cookie_scheme, cookie_param = get_authorization_scheme_param(
            cookie_authorization
        )

        if header_scheme.lower() == "bearer":
            authorization = True
            scheme = header_scheme
            param = header_param

        elif cookie_scheme.lower() == "bearer":
            authorization = True
            scheme = cookie_scheme
            param = cookie_param

        else:
            authorization = False

        if not authorization or scheme.lower() != "bearer": # pylint: disable=E0606
            if self.auto_error:
                raise HTTPException(
                    status_code=HTTP_403_FORBIDDEN, detail="Not authenticated"
                )
            else:
                return None
        return param # pylint: disable=E0606

class BasicAuth(SecurityBase):
    def __init__(self, scheme_name: str = None, auto_error: bool = True):
        self.scheme_name = scheme_name or self.__class__.__name__
        self.model = SecurityBaseModel(type="http")
        self.auto_error = auto_error

    async def __call__(self, request: Request) -> Optional[str]:
        authorization: str = request.headers.get("Authorization")
        scheme, param = get_authorization_scheme_param(authorization)
        if not authorization or scheme.lower() != "basic":
            if self.auto_error:
                raise HTTPException(
                    status_code=HTTP_403_FORBIDDEN, detail="Not authenticated"
                )
            else:
                return None
        return param

basic_auth = BasicAuth(auto_error=False)

pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto")

oauth2_scheme = OAuth2PasswordBearerCookie(tokenUrl="/token")

app = FastAPI(docs_url=None, redoc_url=None, openapi_url=None, title="OpenMPTCProuter Server API")


def create_access_token(*, data: dict, expires_delta: timedelta = None):
    to_encode = data.copy()
    if expires_delta:
        expire = datetime.utcnow() + expires_delta
    else:
        expire = datetime.utcnow() + timedelta(minutes=60)
    to_encode.update({"exp": expire})
    encoded_jwt = jwt.encode(to_encode, SECRET_KEY, algorithm=ALGORITHM)
    return encoded_jwt

async def get_current_user(token: str = Depends(oauth2_scheme)):
    credentials_exception = HTTPException(
        status_code=HTTP_403_FORBIDDEN,
        detail="Could not validate credentials",
        headers={"WWW-Authenticate": "Bearer"},
    )
    try:
        payload = jwt.decode(token, SECRET_KEY, algorithms=[ALGORITHM])
        username: str = payload.get("sub")
        if username not in ALLOWED_AUTH_IDENTITIES:
            LOG.debug("get_current_user: Username not found")
            raise credentials_exception
        token_data = TokenData(username=username)
    except PyJWTError:
        LOG.debug("PyJWTError")
        raise credentials_exception
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        omr_config_data = json.load(f)
    fake_users_db = omr_config_data['users'][0]
    LOG.debug('token user: ' + token_data.username)
    user = get_user(fake_users_db, username=token_data.username)
    if user is None:
        LOG.debug("user is none")
        raise credentials_exception
    return user

async def get_current_active_user(current_user: User = Depends(get_current_user)):
    if current_user.disabled:
        raise HTTPException(status_code=400, detail="Inactive user")
    return current_user

# Show something at homepage
@app.get("/")
async def homepage():
    return "Welcome to OpenMPTCProuter Server part"

# Provide a method to create access tokens. The create_jwt()
# function is used to actually generate the token
@app.post('/token', response_model=Token)
async def login_for_access_token(form_data: OAuth2PasswordRequestForm = Depends()):
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        omr_config_data = json.load(f)
    fake_users_db = omr_config_data['users'][0]

    user = authenticate_user(fake_users_db, form_data.username, form_data.password)
    if not user:
        LOG.debug("Incorrect username or password")
        raise HTTPException(status_code=400, detail="Incorrect username or password")

    # Identity can be any data that is json serializable
    access_token_expires = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    access_token = create_access_token(
        data={"sub": form_data.username}, expires_delta=access_token_expires
    )
    return {"access_token": access_token, "token_type": "bearer"}

@app.get("/logout")
async def route_logout_and_remove_cookie():
    response = RedirectResponse(url="/")
    response.delete_cookie("Authorization")
    return response


# Login for doc
@app.get("/login_basic")
async def login_basic(auth: BasicAuth = Depends(basic_auth)):
    if not auth:
        response = Response(headers={"WWW-Authenticate": "Basic"}, status_code=401)
        return response

    try:
        decoded = base64.b64decode(auth).decode("ascii")
        username, _, password = decoded.partition(":")
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
            omr_config_data = json.load(f)
            fake_users_db = omr_config_data['users'][0]

        user = authenticate_user(fake_users_db, username, password)
        if not user:
            raise HTTPException(status_code=400, detail="Incorrect email or password")

        access_token_expires = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
        access_token = create_access_token(
            data={"sub": username}, expires_delta=access_token_expires
        )

        token = jsonable_encoder(access_token)

        response = RedirectResponse(url="/docs")
        response.set_cookie(
            "Authorization",
            value=f"Bearer {token}",
            httponly=True,
            max_age=1800,
            expires=1800,
        )
        return response

    except:
        response = Response(headers={"WWW-Authenticate": "Basic"}, status_code=401)
        return response


@app.get("/openapi.json")
async def get_open_api_endpoint(current_user: User = Depends(get_current_active_user)):
    return JSONResponse(get_openapi(title="OpenMPTCProuter Server API", version="2.0.0", routes=app.routes))


@app.get("/docs")
async def get_documentation(current_user: User = Depends(get_current_active_user)):
    return get_swagger_ui_html(openapi_url="/openapi.json", title="docs")

# Get Client IP
@app.get('/clienthost')
async def clienthost(request: Request):
    client_host = request.client.host
    return {"client_host": client_host}

# Check if MPTCP is enabled on this connection
@app.get('/mptcpsupport')
async def mptcpsupport(request: Request):
    ip = request.client.host
    if type(ip_address(ip)) is IPv6Address:
        ip = str(ip_address(ip).ipv4_mapped)
    if type(ip_address(ip)) is IPv4Address:
        ipr = list(reversed(ip.split('.')))
        iptohex = '{:02X}{:02X}{:02X}{:02X}'.format(*map(int, ipr))
        if path.exists('/proc/net/mptcp_net/mptcp'):
            with open('/proc/net/mptcp_net/mptcp') as f:
                if iptohex in f.read():
                    return {"mptcp": "working"}
        else:
            mptcpcheck = subprocess.Popen("timeout 2 ss -M | grep -q " + ip, shell=True, stdout=subprocess.PIPE)
            mptcpcheck.communicate()
            if mptcpcheck.returncode == 0:
                return {"mptcp": "working"}
            mptcpcheck.kill()
        return {"mptcp": "not working"}
    return {"mptcp": "check only support IPv4"}

# Get VPS status
@app.get('/status', summary="Get current server load average, uptime and release")
async def status(serial: Optional[str] = Query(None), current_user: User = Depends(get_current_user)):
    LOG.debug('Get status...')
    userid = 0
    username = PRIMARY_ROUTER_USERNAME
    if not current_user.permissions == "admin" and serial is not None:
        if not check_username_serial(username, serial):
            return {'error': 'False serial number'}
    vps_loadavg = os.popen("cat /proc/loadavg | awk '{print $1\" \"$2\" \"$3}'").read().rstrip()
    vps_cpu_count = os.cpu_count()
    vps_memory = psutil.virtual_memory()
    vps_memory_total = vps_memory.total
    vps_memory_available = vps_memory.available
    vps_memory_percent = vps_memory.percent
    vps_memory_used = vps_memory.used
    vps_memory_free = vps_memory.free
    vps_disk = psutil.disk_usage('/')
    vps_disk_total = vps_disk.total
    vps_disk_used = vps_disk.used
    vps_disk_free = vps_disk.free
    vps_disk_percent = vps_disk.percent
    try:
        vps_cpu_freq = psutil.cpu_freq().current
    except:
        vps_cpu_freq = None
    vps_cpu_model = os.popen("cat /proc/cpuinfo | awk -F: '/model name/ {print $2;exit}'").read().strip()
    vps_uptime = os.popen("cat /proc/uptime | awk '{print $1}'").read().rstrip()
    vps_hostname = socket.gethostname()
    vps_current_time = time.time()
    vps_kernel = os.popen('uname -r').read().rstrip()
    vps_omr_version = os.popen("grep -s 'OpenMPTCProuter VPS' /etc/* | awk '{print $4}'").read().rstrip()
    mptcp_enabled = "0"
    if path.exists("/proc/sys/net/mptcp/mptcp_enabled"):
        mptcp_enabled = os.popen('sysctl -qn net.mptcp.mptcp_enabled').read().rstrip()
    elif path.exists("/proc/sys/net/mptcp/enabled"):
        mptcp_enabled = os.popen('sysctl -qn net.mptcp.enabled').read().rstrip()
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    router_user = get_user(omr_config_data['users'][0], PRIMARY_ROUTER_USERNAME)
    if router_user is None:
        return {'error': 'Primary router user not configured', 'route': 'status'}
    proxy = 'shadowsocks'
    if 'proxy' in omr_config_data['users'][0][username]:
        proxy = omr_config_data['users'][0][username]['proxy']
    shadowsocks_port = router_user.shadowsocks_port
    if not shadowsocks_port == None and proxy == 'shadowsocks':
        ss_traffic = get_bytes_ss(shadowsocks_port)
    else:
        ss_traffic = 0
    ss_go_tx = 0
    ss_go_rx = 0
    if os.path.isfile('/etc/shadowsocks-go/server.json') and ('shadowsocks-go' in proxy or 'shadowsocks-rust' in proxy) and checkIfProcessRunning('shadowsocks-go'):
        ss_go_txrx = get_bytes_ss_go(username)
        ss_go_tx = ss_go_txrx['downlinkBytes']
        ss_go_rx = ss_go_txrx['uplinkBytes']
    v2ray_tx = 0
    v2ray_rx = 0
    if os.path.isfile('/etc/v2ray/v2ray-server.json') and 'v2ray' in proxy and checkIfProcessRunning('v2ray'):
        v2ray_tx = get_bytes_v2ray('tx',username)
        v2ray_rx = get_bytes_v2ray('rx',username)
    xray_tx = 0
    xray_rx = 0
    if os.path.isfile('/etc/xray/xray-server.json') and 'xray' in proxy and checkIfProcessRunning('xray'):
        xray_tx = get_bytes_xray('tx',username)
        xray_rx = get_bytes_xray('rx',username)
    vpn = 'glorytun_tcp'
    if 'vpn' in omr_config_data['users'][0][username]:
        vpn = omr_config_data['users'][0][username]['vpn']
    vpn_traffic_rx = 0
    vpn_traffic_tx = 0
    if vpn == 'glorytun_tcp':
        vpn_traffic_rx = get_bytes('rx', 'gt-tun' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'gt-tun' + str(userid))
    elif vpn == 'glorytun_udp':
        vpn_traffic_rx = get_bytes('rx', 'gt-udp-tun' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'gt-udp-tun' + str(userid))
    elif vpn == 'mqvpn':
        vpn_traffic_rx = get_bytes('rx', 'mqvpn0')
        vpn_traffic_tx = get_bytes('tx', 'mqvpn0')
    elif vpn == 'mqvpn2':
        vpn_traffic_rx = get_bytes('rx', 'mqvpn2')
        vpn_traffic_tx = get_bytes('tx', 'mqvpn2')
    elif vpn == 'dsvpn':
        vpn_traffic_rx = get_bytes('rx', 'dsvpn' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'dsvpn' + str(userid))
    elif vpn == 'openvpn':
        # vpn_traffic_rx = get_bytes('rx', 'tun0')
        # vpn_traffic_tx = get_bytes('tx', 'tun0')
        vpn_txrx = get_bytes_openvpn(username)
        vpn_traffic_rx = vpn_txrx['uplinkBytes']
        vpn_traffic_tx = vpn_txrx['downlinkBytes']
    elif vpn == 'openvpn_bonding':
        vpn_traffic_rx = get_bytes('rx', 'omr-bonding')
        vpn_traffic_tx = get_bytes('tx', 'omr-bonding')
    elif vpn == 'softether':
        vpn_txrx = get_bytes_softether(username)
        vpn_traffic_rx = vpn_txrx['uplinkBytes']
        vpn_traffic_tx = vpn_txrx['downlinkBytes']

    LOG.debug('Get status: done')
    if IFACE:
        return {'vps': {'time': vps_current_time, 'loadavg': vps_loadavg,'cpu_model': vps_cpu_model, 'cpu_count': vps_cpu_count, 'memory_total': vps_memory_total, 'memory_available': vps_memory_available, 'memory_percent': vps_memory_percent, 'memory_used': vps_memory_used, 'memory_free': vps_memory_free,'disk_total': vps_disk_total, 'disk_used': vps_disk_used, 'disk_free': vps_disk_free, 'disk_percent': vps_disk_percent, 'cpu_freq': vps_cpu_freq, 'uptime': vps_uptime, 'mptcp': mptcp_enabled, 'hostname': vps_hostname, 'kernel': vps_kernel, 'omr_version': vps_omr_version}, 'network': {'tx': get_bytes('tx', IFACE), 'rx': get_bytes('rx', IFACE)}, 'shadowsocks': {'traffic': ss_traffic}, 'vpn': {'tx': vpn_traffic_tx, 'rx': vpn_traffic_rx}, 'v2ray': {'tx': v2ray_tx, 'rx': v2ray_rx},'xray': {'tx': xray_tx, 'rx': xray_rx},'shadowsocks_go': {'tx': ss_go_tx, 'rx': ss_go_rx}}
    else:
        return {'error': 'No iface defined', 'route': 'status'}

# Get VPS config
@app.get('/config', summary="Get full server configuration for current user")
async def config(serial: Optional[str] = Query(None), current_user: User = Depends(get_current_user)):
    LOG.debug('Get config...')
    userid = 0
    username = PRIMARY_ROUTER_USERNAME
    if not current_user.permissions == "admin" and serial is not None:
        if not check_username_serial(username, serial):
            return {'error': 'False serial number'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
                try:
                    omr_config_data = json.load(f)
                except ValueError as e:
                    omr_config_data = {}
    router_user = get_user(omr_config_data['users'][0], PRIMARY_ROUTER_USERNAME)
    if router_user is None:
        return {'error': 'Primary router user not configured', 'route': 'config'}
    LOG.debug('Get config... shadowsocks')
    proxy = 'shadowsocks'
    if 'proxy' in omr_config_data['users'][0][username]:
        proxy = omr_config_data['users'][0][username]['proxy']

    if os.path.isfile('/etc/shadowsocks-libev/manager.json'):
        with open('/etc/shadowsocks-libev/manager.json') as f:
            content = f.read()
        content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
        try:
            data = json.loads(content)
        except ValueError as e:
            data = {'server_port': 65101, 'method': 'chacha20'}
    else:
        data = {'server_port': 65101, 'method': 'chacha20'}
    #shadowsocks_port = data["server_port"]
    shadowsocks_port = router_user.shadowsocks_port
    shadowsocks_key = ''
    if shadowsocks_port is not None:
        if 'port_key' in data:
            shadowsocks_key = data["port_key"][str(shadowsocks_port)]
        elif 'port_conf' in data:
            shadowsocks_key = data["port_conf"][str(shadowsocks_port)]["key"]
    shadowsocks_method = data["method"]
    if 'fast_open' in data:
        shadowsocks_fast_open = data["fast_open"]
    else:
        shadowsocks_fast_open = False
    if 'reuse_port' in data:
        shadowsocks_reuse_port = data["reuse_port"]
    else:
        shadowsocks_reuse_port = False
    if 'no_delay' in data:
        shadowsocks_no_delay = data["no_delay"]
    else:
        shadowsocks_no_delay = False
    if 'mptcp' in data:
        shadowsocks_mptcp = data["mptcp"]
    else:
        shadowsocks_mptcp = False
    if 'ebpf' in data:
        shadowsocks_ebpf = data["ebpf"]
    else:
        shadowsocks_ebpf = False
    if "plugin" in data:
        shadowsocks_obfs = True
        if 'v2ray' in data["plugin"]:
            shadowsocks_obfs_plugin = 'v2ray'
        else:
            shadowsocks_obfs_plugin = 'obfs'
        if 'tls' in data["plugin_opts"]:
            shadowsocks_obfs_type = 'tls'
        else:
            shadowsocks_obfs_type = 'http'
    else:
        shadowsocks_obfs = False
        shadowsocks_obfs_plugin = ''
        shadowsocks_obfs_type = ''
    shadowsocks_port = router_user.shadowsocks_port
    if not shadowsocks_port == None and proxy == 'shadowsocks':
        ss_traffic = get_bytes_ss(shadowsocks_port)
    else:
        ss_traffic = 0

    LOG.debug('Get config... glorytun')
    if os.path.isfile('/etc/glorytun-tcp/tun' + str(userid) +'.key'):
        glorytun_key = open('/etc/glorytun-tcp/tun' + str(userid) + '.key').readline().rstrip()
    elif os.path.isfile('/etc/glorytun-udp/tun' + str(userid) +'.key'):
        glorytun_key = open('/etc/glorytun-udp/tun' + str(userid) + '.key').readline().rstrip()
    else:
        glorytun_key = ''
    glorytun_port = '65001'
    glorytun_chacha = False
    glorytun_tcp_host_ip = ''
    glorytun_tcp_client_ip = ''
    glorytun_udp_host_ip = ''
    glorytun_udp_client_ip = ''
    if os.path.isfile('/etc/glorytun-tcp/tun' + str(userid)):
        with open('/etc/glorytun-tcp/tun' + str(userid), "r") as glorytun_file:
            for line in glorytun_file:
                if 'PORT=' in line:
                    glorytun_port = line.replace(line[:5], '').rstrip()
                if 'LOCALIP=' in line:
                    glorytun_tcp_host_ip = line.replace(line[:8], '').rstrip()
                if 'REMOTEIP=' in line:
                    glorytun_tcp_client_ip = line.replace(line[:9], '').rstrip()
                if 'chacha' in line:
                    glorytun_chacha = True
    if userid == 0 and glorytun_tcp_host_ip == '':
        if 'glorytun_tcp_type' in omr_config_data:
            if omr_config_data['glorytun_tcp_type'] == 'static':
                glorytun_tcp_host_ip = '10.255.255.1'
                glorytun_tcp_client_ip = '10.255.255.2'
            else:
                glorytun_tcp_host_ip = 'dhcp'
                glorytun_tcp_client_ip = 'dhcp'
        else:
            glorytun_tcp_host_ip = '10.255.255.1'
            glorytun_tcp_client_ip = '10.255.255.2'
    if os.path.isfile('/etc/glorytun-udp/tun' + str(userid)):
        with open('/etc/glorytun-udp/tun' + str(userid), "r") as glorytun_file:
            for line in glorytun_file:
                if 'LOCALIP=' in line:
                    glorytun_udp_host_ip = line.replace(line[:8], '').rstrip()
                if 'REMOTEIP=' in line:
                    glorytun_udp_client_ip = line.replace(line[:9], '').rstrip()

    if userid == 0 and glorytun_udp_host_ip == '':
        if 'glorytun_udp_type' in omr_config_data:
            if omr_config_data['glorytun_udp_type'] == 'static':
                glorytun_udp_host_ip = '10.255.254.1'
                glorytun_udp_client_ip = '10.255.254.2'
            else:
                glorytun_udp_host_ip = 'dhcp'
                glorytun_udp_client_ip = 'dhcp'
        else:
            glorytun_udp_host_ip = '10.255.254.1'
            glorytun_udp_client_ip = '10.255.254.2'
    available_vpn = ["glorytun_tcp", "glorytun_udp"]
    LOG.debug('Get config... dsvpn')
    if os.path.isfile('/etc/dsvpn/dsvpn' + str(userid) + '.key'):
        dsvpn_key = open('/etc/dsvpn/dsvpn' + str(userid) + '.key').readline().rstrip()
        available_vpn.append("dsvpn")
    else:
        dsvpn_key = ''
    dsvpn_port = '65401'
    dsvpn_host_ip = ''
    dsvpn_client_ip = ''
    if os.path.isfile('/etc/dsvpn/dsvpn' + str(userid)):
        with open('/etc/dsvpn/dsvpn' + str(userid), "r") as dsvpn_file:
            for line in dsvpn_file:
                if 'PORT=' in line:
                    dsvpn_port = line.replace(line[:5], '').rstrip()
                if 'LOCALTUNIP=' in line:
                    dsvpn_host_ip = line.replace(line[:11], '').rstrip()
                if 'REMOTETUNIP=' in line:
                    dsvpn_client_ip = line.replace(line[:12], '').rstrip()

    if userid == 0 and dsvpn_host_ip == '':
        dsvpn_host_ip = '10.255.251.1'
        dsvpn_client_ip = '10.255.251.2'

    LOG.debug('Get config... iperf3')
    if os.path.isfile('/etc/iperf3/public.pem'):
        with open('/etc/iperf3/public.pem', "rb") as iperfkey_file:
            iperf_keyb = base64.b64encode(iperfkey_file.read())
            iperf3_key = iperf_keyb.decode('utf-8')
    else:
        iperf3_key = ''

    LOG.debug('Get config... openvpn')
    #if os.path.isfile('/etc/openvpn/server/static.key'):
    #    with open('/etc/openvpn/server/static.key',"rb") as ovpnkey_file:
    #        openvpn_keyb = base64.b64encode(ovpnkey_file.read())
    #        openvpn_key = openvpn_keyb.decode('utf-8')
    #    available_vpn.append("openvpn")
    #else:
    #    openvpn_key = ''
    openvpn_key = ''
    if os.path.isfile('/etc/openvpn/ca/pki/private/' + username + '.key'):
        with open('/etc/openvpn/ca/pki/private/' + username + '.key', "rb") as ovpnkey_file:
            openvpn_keyb = base64.b64encode(ovpnkey_file.read())
            openvpn_client_key = openvpn_keyb.decode('utf-8')
    else:
        openvpn_client_key = ''
    if os.path.isfile('/etc/openvpn/ca/pki/issued/' + username + '.crt'):
        with open('/etc/openvpn/ca/pki/issued/' + username + '.crt', "rb") as ovpnkey_file:
            openvpn_keyb = base64.b64encode(ovpnkey_file.read())
            openvpn_client_crt = openvpn_keyb.decode('utf-8')
        available_vpn.append("openvpn")
    else:
        openvpn_client_crt = ''
    if os.path.isfile('/etc/openvpn/ca/pki/ca.crt'):
        with open('/etc/openvpn/ca/pki/ca.crt', "rb") as ovpnkey_file:
            openvpn_keyb = base64.b64encode(ovpnkey_file.read())
            openvpn_client_ca = openvpn_keyb.decode('utf-8')
    else:
        openvpn_client_ca = ''
    openvpn_port = '65301'
    openvpn_cipher = 'AES-256-GCM'
    if os.path.isfile('/etc/openvpn/tun0.conf'):
        with open('/etc/openvpn/tun0.conf', "r") as openvpn_file:
            for line in openvpn_file:
                if 'port ' in line:
                    openvpn_port = line.replace(line[:5], '').rstrip()
                if 'cipher ' in line:
                    openvpn_cipher = line.replace(line[:7], '').rstrip()
    openvpn_host_ip = '10.255.252.1'
    #openvpn_client_ip = '10.255.252.2'
    openvpn_client_ip = 'dhcp'

    if os.path.isfile('/etc/openvpn/bonding1.conf'):
        available_vpn.append("openvpn_bonding")

    softether = False
    if os.path.isfile('/var/lib/softether/vpn_server.config'):
        available_vpn.append("softether")
        softether = True
    softether_password = ''
    if 'softethervpn' in omr_config_data['users'][0][username]:
        softether_password = omr_config_data['users'][0][username]['softethervpn']
    softether_port = '65390'
    softether_cipher = 'AES-256-GCM'
    softether_host_ip = '10.255.210.1'
    softether_client_ip = 'dhcp'

    LOG.debug('Get config... mqvpn')
    mqvpn_key = ''
    mqvpn_port = '65411'
    mqvpn_scheduler = 'wlb'
    mqvpn_cc = 'cubic'
    mqvpn_mtu = 0
    mqvpn_outer_packet_size = 1400
    mqvpn_pmtud = False
    mqvpn_pmtud_probe_size = 1420
    mqvpn_log_level = 'info'
    mqvpn_host_ip = '10.255.249.1'
    mqvpn_client_ip = '10.255.249.2'
    if os.path.isfile('/etc/mqvpn/server.conf'):
        mqvpn_config = configparser.ConfigParser(strict=False)
        mqvpn_config.optionxform = str
        mqvpn_config.read_file(open(r'/etc/mqvpn/server.conf'))
        if mqvpn_config.has_option('Auth', 'Key'):
            mqvpn_key = mqvpn_config.get('Auth', 'Key')
        if mqvpn_config.has_option('Interface', 'Listen'):
            mqvpn_listen = mqvpn_config.get('Interface', 'Listen')
            if ':' in mqvpn_listen:
                mqvpn_port = mqvpn_listen.rsplit(':', 1)[1]
        if mqvpn_config.has_option('Interface', 'Subnet'):
            try:
                mqvpn_subnet = IPNetwork(mqvpn_config.get('Interface', 'Subnet'))
                if mqvpn_subnet.version == 4 and mqvpn_subnet.size >= 4:
                    mqvpn_host_ip = str(mqvpn_subnet[1])
                    mqvpn_client_ip = str(mqvpn_subnet[2])
            except (AddrFormatError, ValueError):
                LOG.warning('Invalid MQVPN Interface.Subnet; reporting default tunnel IPs')
        if mqvpn_config.has_option('Multipath', 'Scheduler'):
            mqvpn_scheduler = mqvpn_config.get('Multipath', 'Scheduler')
        if mqvpn_config.has_option('Multipath', 'CC'):
            mqvpn_cc = mqvpn_config.get('Multipath', 'CC')
        if mqvpn_config.has_option('Interface', 'MTU'):
            try:
                mqvpn_mtu = mqvpn_config.getint('Interface', 'MTU')
            except ValueError:
                LOG.warning('Invalid MQVPN Interface.MTU; reporting safe default')
        if mqvpn_config.has_option('Interface', 'LogLevel'):
            mqvpn_log_level = mqvpn_config.get('Interface', 'LogLevel')
        if mqvpn_config.has_option('Multipath', 'OuterPacketSize'):
            try:
                mqvpn_outer_packet_size = mqvpn_config.getint('Multipath', 'OuterPacketSize')
            except ValueError:
                LOG.warning('Invalid MQVPN Multipath.OuterPacketSize; reporting safe default')
        if mqvpn_config.has_option('Multipath', 'PMTUD'):
            try:
                mqvpn_pmtud = mqvpn_config.getboolean('Multipath', 'PMTUD')
            except ValueError:
                LOG.warning('Invalid MQVPN Multipath.PMTUD; reporting safe default')
        if mqvpn_config.has_option('Multipath', 'PMTUDProbeSize'):
            try:
                mqvpn_pmtud_probe_size = mqvpn_config.getint('Multipath', 'PMTUDProbeSize')
            except ValueError:
                LOG.warning('Invalid MQVPN Multipath.PMTUDProbeSize; reporting safe default')
        available_vpn.append("mqvpn")

    LOG.debug('Get config... mqvpn2')
    mqvpn2_key = ''
    mqvpn2_port = '65412'
    mqvpn2_scheduler = 'wlb'
    mqvpn2_cc = 'cubic'
    mqvpn2_mtu = 0
    mqvpn2_init_max_path_id = 128
    mqvpn2_reorder = False
    mqvpn2_log_level = 'info'
    mqvpn2_host_ip = '10.255.248.1'
    mqvpn2_client_ip = '10.255.248.2'
    if os.path.isfile('/etc/mqvpn2/server.conf'):
        mqvpn2_config = configparser.ConfigParser(strict=False)
        mqvpn2_config.optionxform = str
        mqvpn2_config.read_file(open(r'/etc/mqvpn2/server.conf'))
        if mqvpn2_config.has_option('Auth', 'Key'):
            mqvpn2_key = mqvpn2_config.get('Auth', 'Key')
        if mqvpn2_config.has_option('Interface', 'Listen'):
            mqvpn2_listen = mqvpn2_config.get('Interface', 'Listen')
            if ':' in mqvpn2_listen:
                mqvpn2_port = mqvpn2_listen.rsplit(':', 1)[1]
        if mqvpn2_config.has_option('Interface', 'Subnet'):
            try:
                mqvpn2_subnet = IPNetwork(mqvpn2_config.get('Interface', 'Subnet'))
                if mqvpn2_subnet.version == 4 and mqvpn2_subnet.size >= 4:
                    mqvpn2_host_ip = str(mqvpn2_subnet[1])
                    mqvpn2_client_ip = str(mqvpn2_subnet[2])
            except (AddrFormatError, ValueError):
                LOG.warning('Invalid MQVPN2 Interface.Subnet; reporting defaults')
        if mqvpn2_config.has_option('Multipath', 'Scheduler'):
            mqvpn2_scheduler = mqvpn2_config.get('Multipath', 'Scheduler')
        if mqvpn2_config.has_option('Multipath', 'CC'):
            mqvpn2_cc = mqvpn2_config.get('Multipath', 'CC')
        if mqvpn2_config.has_option('Interface', 'MTU'):
            try:
                mqvpn2_mtu = mqvpn2_config.getint('Interface', 'MTU')
            except ValueError:
                LOG.warning('Invalid MQVPN2 Interface.MTU; reporting default')
        if mqvpn2_config.has_option('Multipath', 'InitMaxPathId'):
            try:
                mqvpn2_init_max_path_id = mqvpn2_config.getint(
                    'Multipath', 'InitMaxPathId')
            except ValueError:
                LOG.warning('Invalid MQVPN2 InitMaxPathId; reporting default')
        if mqvpn2_config.has_option('Reorder', 'Enabled'):
            mqvpn2_reorder = mqvpn2_config.get(
                'Reorder', 'Enabled').lower() in ['1', 'true', 'yes', 'on']
        if mqvpn2_config.has_option('Interface', 'LogLevel'):
            mqvpn2_log_level = mqvpn2_config.get('Interface', 'LogLevel')
        available_vpn.append("mqvpn2")

    LOG.debug('Get config... wireguard')
    if os.path.isfile('/etc/wireguard/vpn-server-public.key'):
        with open('/etc/wireguard/vpn-server-public.key', "rb") as wgkey_file:
            wireguard_key = wgkey_file.read()
    else:
        wireguard_key = ''
    wireguard_host_ip = '10.255.247.1'
    wireguard_port = '65311'

    LOG.debug('Get config... wireguard for external clients')
    if os.path.isfile('/etc/wireguard/vpn-client-private.key'):
        with open('/etc/wireguard/vpn-client-private.key', "rb") as wgkey_file:
            wireguard_client_key = wgkey_file.read()
    else:
        wireguard_client_key = ''
    wireguard_client_ip = '10.255.246.2'
    wireguard_client_port = '65312'

    gre_tunnel = False
    gre_tunnel_conf = []
#    for tunnel in pathlib.Path('/etc/openmptcprouter-vps-admin/intf').glob('gre-user' + str(userid) + '-ip*'):
#        gre_tunnel = True
#        with open(tunnel, "r") as tunnel_conf:
#            for line in tunnel_conf:
#                if 'LOCALIP=' in line:
#                    gre_tunnel_localip = line.replace(line[:8], '').rstrip()
#                if 'REMOTEIP=' in line:
#                    gre_tunnel_remoteip = line.replace(line[:9], '').rstrip()
#                if 'NETMASK=' in line:
#                    gre_tunnel_netmask = line.replace(line[:8], '').rstrip()
#                if 'INTFADDR=' in line:
#                    gre_tunnel_intfaddr = line.replace(line[:9], '').rstrip()
#        gre_tunnel_conf.append("{'local_ip': '" + gre_tunnel_localip + "', 'remote_ip': '" + gre_tunnel_remoteip + "', 'netmask': '" + gre_tunnel_netmask + "', 'public_ip': '" + gre_tunnel_intfaddr + "'}")

    LOG.debug("Gre tunnels... ?")
    LOG.debug(omr_config_data['users'][0][username])
    if 'gre_tunnels' in omr_config_data['users'][0][username]:
        LOG.debug("Gre tunnels...")
        gre_tunnel = True
        gre_tunnel_conf = omr_config_data['users'][0][username]['gre_tunnels']

    if 'vpnremoteip' in omr_config_data['users'][0][username]:
        vpn_remote_ip = omr_config_data['users'][0][username]['vpnremoteip']
    else:
        vpn_remote_ip = ''
    if 'vpnlocalip' in omr_config_data['users'][0][username]:
        vpn_local_ip = omr_config_data['users'][0][username]['vpnlocalip']
    else:
        vpn_local_ip = ''

    v2ray = False
    v2ray_conf = []
    v2ray_tx = 0
    v2ray_rx = 0
    if os.path.isfile('/etc/v2ray/v2ray-server.json'):
        v2ray = True
        if not 'v2ray' in omr_config_data['users'][0][username]:
            v2ray_key = os.popen("jq -r '.inbounds[0].settings.clients[] | select(.email==" + '"' + username + '"' + ") | .id' /etc/v2ray/v2ray-server.json").read().rstrip()
            v2ray_port = os.popen('jq -r .inbounds[0].port /etc/v2ray/v2ray-server.json').read().rstrip()
            v2ray_conf = { 'key': v2ray_key, 'port': v2ray_port}
            LOG.debug("modif_config_user for v2ray")
            modif_config_user(username, {'v2ray': v2ray_conf})
        else:
            v2ray_conf = omr_config_data['users'][0][username]['v2ray']
        if checkIfProcessRunning('v2ray') and proxy == 'v2ray':
            v2ray_tx = get_bytes_v2ray('tx',username)
            v2ray_rx = get_bytes_v2ray('rx',username)

    xray = False
    xray_conf = []
    xray_tx = 0
    xray_rx = 0
    if os.path.isfile('/etc/xray/xray-server.json'):
        xray = True
        if not 'xray' in omr_config_data['users'][0][username]:
            xray_key = os.popen("jq -r '.inbounds[0].settings.clients[] | select(.email==" + '"' + username + '"' + ") | .id' /etc/xray/xray-server.json").read().rstrip()
            xray_ss_skey = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-shadowsocks-tunnel' + '"' + ") | .settings.password' /etc/xray/xray-server.json").read().rstrip()
            xray_ss_ukey = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-shadowsocks-tunnel' + '"' + ") | .settings.clients[] | select(.email==" + '"' + username + '"' + ") | .password' /etc/xray/xray-server.json").read().rstrip()
            xray_ss_key = xray_ss_skey + ':' + xray_ss_ukey
            xray_port = os.popen('jq -r .inbounds[0].port /etc/xray/xray-server.json').read().rstrip()
            xray_ss_method = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-shadowsocks-tunnel' + '"' + ") | .settings.method' /etc/xray/xray-server.json").read().rstrip()
            xray_transport = os.popen("jq -r '(.inbounds[0].streamSettings.network)' /etc/xrayxray-server.json").read().rstrip()
            xray_vless_reality_public_key = ''
            if os.path.isfile('/etc/xray/xray-vless-reality.json'):
                xray_vless_reality_public_key = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-vless-reality' + '"' + ") | .streamSettings.realitySettings.publicKey' /etc/xray/xray-vless-reality.json").read().rstrip()
            test_vless_reality = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-vless-reality' + '"' + ")' /etc/xray/xray-server.json").read().rstrip()
            if test_vless_reality != '':
                vless_reality = True
            else:
                vless_reality = False
            xray_conf = { 'key': xray_key, 'port': xray_port, 'sskey': xray_ss_key, 'vless_reality': vless_reality, 'vless_reality_key': xray_vless_reality_public_key, 'ss_method': xray_ss_method, 'transport': xray_transport }
            LOG.debug("modif_config_user for xray")
            modif_config_user(username, {'xray': xray_conf})
        else:
            xray_conf = omr_config_data['users'][0][username]['xray']
        if checkIfProcessRunning('xray') and proxy == 'xray':
            xray_tx = get_bytes_xray('tx',username)
            xray_rx = get_bytes_xray('rx',username)

    shadowsocks_go = False
    shadowsocks_go_conf = []
    ss_go_tx = 0
    ss_go_rx = 0
    if os.path.isfile('/etc/shadowsocks-go/server.json'):
        shadowsocks_go = True
        if not 'shadowsocks-go' in omr_config_data['users'][0][username]:
            shadowsocks_go_psk = os.popen("jq -r '.servers[] | select(.name==" + '"ss-2022"' + ") | .psk' /etc/shadowsocks-go/server.json").read().rstrip()
            shadowsocks_go_port = os.popen("jq -r '.servers[] | select(.name==" + '"ss-2022"' + ") | .tcpListeners[0].address' /etc/shadowsocks-go/server.json | cut -d ':' -f2").read().rstrip()
            shadowsocks_go_protocol = os.popen("jq -r '.servers[] | select(.name==" + '"ss-2022"' + ") | .protocol' /etc/shadowsocks-go/server.json").read().rstrip()
            shadowsocks_go_upsk = os.popen("jq -r --arg user " + '"' + username + '"' + " '.[$user]' /etc/shadowsocks-go/upsks.json").read().rstrip()
            shadowsocks_go_conf= { 'password': shadowsocks_go_psk + ':' + shadowsocks_go_upsk, 'port': shadowsocks_go_port, 'protocol': shadowsocks_go_protocol }
            LOG.debug("modif_config_user for shadowsocks-go")
            modif_config_user(username, {'shadowsocks-go': shadowsocks_go_conf})
        else:
            shadowsocks_go_conf = omr_config_data['users'][0][username]['shadowsocks-go']
        ss_go_txrx = get_bytes_ss_go(username)
        ss_go_tx = int(ss_go_txrx['downlinkBytes'])
        ss_go_rx = int(ss_go_txrx['uplinkBytes'])

    LOG.debug('Get config... mptcp')
    mptcp_version = mptcp_enabled = mptcp_checksum = '0'
    mptcp_path_manager = mptcp_scheduler = mptcp_syn_retries = ''
    if path.exists('/proc/sys/net/mptcp/mptcp_enabled'):
        mptcp_enabled = os.popen('sysctl -n net.mptcp.mptcp_enabled').read().rstrip()
        mptcp_checksum = os.popen('sysctl -n net.mptcp.mptcp_checksum').read().rstrip()
        mptcp_path_manager = os.popen('sysctl -n  net.mptcp.mptcp_path_manager').read().rstrip()
        mptcp_scheduler = os.popen('sysctl -n net.mptcp.mptcp_scheduler').read().rstrip()
        mptcp_syn_retries = os.popen('sysctl -n net.mptcp.mptcp_syn_retries').read().rstrip()
        mptcp_version = os.popen('sysctl -n net.mptcp.mptcp_version').read().rstrip()
    elif path.exists('/proc/sys/net/mptcp/enabled'):
        mptcp_enabled = os.popen('sysctl -n net.mptcp.enabled').read().rstrip()
        mptcp_checksum = os.popen('sysctl -n net.mptcp.checksum_enabled').read().rstrip()
        mptcp_version = '1'

    congestion_control = os.popen('sysctl -n net.ipv4.tcp_congestion_control').read().rstrip()
    nanbbr_var_capabilities = nanbbr_capabilities()
    nanbbr_aggressiveness = read_nanbbr_aggressiveness()
    selected_nanbbr_parameter = nanbbr_parameter_path(congestion_control)
    if selected_nanbbr_parameter and path.exists(selected_nanbbr_parameter):
        try:
            with open(selected_nanbbr_parameter, 'r') as parameter_file:
                runtime_aggressiveness = int(parameter_file.read().strip())
            if NANBBR_AGGRESSIVENESS_MIN <= runtime_aggressiveness <= NANBBR_AGGRESSIVENESS_MAX:
                nanbbr_aggressiveness = runtime_aggressiveness
        except (OSError, ValueError):
            pass
    if nanbbr_aggressiveness is None:
        for nanbbr_cc, capable in nanbbr_var_capabilities.items():
            if not capable:
                continue
            try:
                with open(nanbbr_parameter_path(nanbbr_cc), 'r') as parameter_file:
                    runtime_aggressiveness = int(parameter_file.read().strip())
                if NANBBR_AGGRESSIVENESS_MIN <= runtime_aggressiveness <= NANBBR_AGGRESSIVENESS_MAX:
                    nanbbr_aggressiveness = runtime_aggressiveness
                    break
            except (OSError, ValueError):
                continue
    if nanbbr_aggressiveness is None and any(nanbbr_var_capabilities.values()):
        nanbbr_aggressiveness = 50
    nanbbr_aggressiveness_capable = nanbbr_var_capabilities.get(
        congestion_control,
        any(nanbbr_var_capabilities.values()),
    )

    LOG.debug('Get config... ipv6')
    if 'ipv6_network' in omr_config_data:
        ipv6_network = omr_config_data['ipv6_network']
    else:
        ipv6_network = os.popen('ip -6 addr show ' + IFACE6 +' | grep -oP "(?<=inet6 ).*(?= scope global)"').read().rstrip()
    if ipv6_network != '':
        set_global_param('ipv6_network', ipv6_network)
    #ipv6_addr = os.popen('wget -6 -qO- -T 2 ipv6.openmptcprouter.com').read().rstrip()
    if 'ipv6_addr' in omr_config_data:
        ipv6_addr = omr_config_data['ipv6_addr']
    else:
        ipv6_addr = os.popen('ip -6 addr show ' + IFACE6 +' | grep -oP "(?<=inet6 ).*(?= scope global)" | cut -d/ -f1').read().rstrip()
    if ipv6_addr != '':
        set_global_param('ipv6_addr', ipv6_addr)
    #ipv4_addr = os.popen('wget -4 -qO- -T 1 https://ip.openmptcprouter.com').read().rstrip()
    LOG.debug('get server IPv4')
    ipv4_addr = ''
    if 'ipv4' in omr_config_data:
        ipv4_addr = omr_config_data['ipv4']
    elif 'internet' in omr_config_data and not omr_config_data['internet']:
        ipv4_addr = os.popen('ip -4 addr show ' + IFACE +' | grep -oP "(?<=inet ).*(?= scope global)" | cut -d/ -f1').read().rstrip()
    else:
        #ipv4_addr = os.popen("dig -4 TXT +timeout=2 +tries=1 +short o-o.myaddr.l.google.com @ns1.google.com | awk -F'\"' '{ print $2}'").read().rstrip()
        if ipv4_addr == '':
            ipv4_addr = os.popen('wget -4 -qO- -t 1 -T 1 http://ip.openmptcprouter.com').read().rstrip()
        if ipv4_addr == '':
            ipv4_addr = os.popen('wget -4 -qO- -t 1 -T 1 http://ifconfig.me').read().rstrip()
        if ipv4_addr != '':
            set_global_param('ipv4', ipv4_addr)

    test_aes = os.popen('cat /proc/cpuinfo | grep aes').read().rstrip()
    if test_aes == '':
        vps_aes = False
    else:
        vps_aes = True
    vps_kernel = os.popen('uname -r').read().rstrip()
    vps_machine = os.popen('uname -m').read().rstrip()
    vps_omr_version = os.popen("grep -s 'OpenMPTCProuter VPS' /etc/* | awk '{print $4}'").read().rstrip()
    vps_loadavg = os.popen("cat /proc/loadavg | awk '{print $1" "$2" "$3}'").read().rstrip()
    vps_uptime = os.popen("cat /proc/uptime | awk '{print $1}'").read().rstrip()
    LOG.debug('get hostname')
    if 'hostname' in omr_config_data:
        vps_domain = omr_config_data['hostname']
    elif 'internet' in omr_config_data and not omr_config_data['internet']:
        vps_domain = ''
    else:
        vps_domain = os.popen('wget -4 -qO- -t 1 -T 1 http://hostname.openmptcprouter.com').read().rstrip()
        if vps_domain != '':
            set_global_param('hostname', vps_domain)
    #vps_domain = os.popen('dig -4 +short +times=3 +tries=1 -x ' + ipv4_addr + " | sed 's/\.$//'").read().rstrip()
    user_permissions = router_user.permissions

    internet = True
    if 'internet' in omr_config_data and not omr_config_data['internet']:
        internet = False

    localip6 = ''
    remoteip6 = ''
    ula = ''
    if userid == 0:
        if os.path.isfile('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid)):
            with open('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid), "r") as omr6in4_file:
                for line in omr6in4_file:
                    if 'LOCALIP6=' in line:
                        localip6 = line.replace(line[:9], '').rstrip()
                    if 'REMOTEIP6=' in line:
                        remoteip6 = line.replace(line[:10], '').rstrip()
                    if 'ULA=' in line:
                        ula = line.replace(line[:4], '').rstrip()
    else:
        locaip6 = 'fd00::a00:1'
        remoteip6 = 'fd00::a00:2'

    vpn = 'openvpn'
    if 'vpn' in omr_config_data['users'][0][username]:
        vpn = omr_config_data['users'][0][username]['vpn']

    vpn_traffic_rx = 0
    vpn_traffic_tx = 0
    if vpn == 'glorytun_tcp':
        vpn_traffic_rx = get_bytes('rx', 'gt-tun' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'gt-tun' + str(userid))
    elif vpn == 'glorytun_udp':
        vpn_traffic_rx = get_bytes('rx', 'gt-udp-tun' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'gt-udp-tun' + str(userid))
    elif vpn == 'mqvpn':
        vpn_traffic_rx = get_bytes('rx', 'mqvpn0')
        vpn_traffic_tx = get_bytes('tx', 'mqvpn0')
    elif vpn == 'mqvpn2':
        vpn_traffic_rx = get_bytes('rx', 'mqvpn2')
        vpn_traffic_tx = get_bytes('tx', 'mqvpn2')
    elif vpn == 'dsvpn':
        vpn_traffic_rx = get_bytes('rx', 'dsvpn' + str(userid))
        vpn_traffic_tx = get_bytes('tx', 'dsvpn' + str(userid))
    elif vpn == 'openvpn':
        #vpn_traffic_rx = get_bytes('rx', 'tun0')
        #vpn_traffic_tx = get_bytes('tx', 'tun0')
        vpn_txrx = get_bytes_openvpn(username)
        vpn_traffic_rx = vpn_txrx['uplinkBytes']
        vpn_traffic_tx = vpn_txrx['downlinkBytes']
    elif vpn == 'openvpn_bonding':
        vpn_traffic_rx = get_bytes('rx', 'omr-bonding')
        vpn_traffic_tx = get_bytes('tx', 'omr-bonding')
    elif vpn == 'softether':
        vpn_txrx = get_bytes_softether(username)
        vpn_traffic_rx = vpn_txrx['uplinkBytes']
        vpn_traffic_tx = vpn_txrx['downlinkBytes']

    available_proxy = ["shadowsocks", "shadowsocks-go","v2ray","v2ray-vmess","v2ray-socks","v2ray-trojan","xray","xray-vless-reality","xray-vmess","xray-socks","xray-trojan","xray-shadowsocks"]
    if user_permissions == 'ro':
        del available_vpn
        available_vpn = [vpn]
        del available_proxy
        available_proxy = [proxy]

    localvpn = ""
    if os.popen('ip l | grep " vpn"').read().rstrip() != '':
        localvpn = "vpn1"

    lanips = ""
    if 'lanips' in omr_config_data['users'][0][username]:
        lanips = omr_config_data['users'][0][username]['lanips']

    shorewall_redirect = "enable"
    with open('/etc/shorewall/rules', 'r') as f:
        for line in f:
            if '#DNAT		net		vpn:$OMR_ADDR	tcp	1-64999' in line:
                shorewall_redirect = "disable"
    LOG.debug('Get config: done')
    return {'vps': {'kernel': vps_kernel, 'machine': vps_machine, 'omr_version': vps_omr_version, 'loadavg': vps_loadavg, 'uptime': vps_uptime, 'aes': vps_aes}, 'lan': {'ips': lanips}, 'shadowsocks': {'traffic': ss_traffic, 'key': shadowsocks_key, 'port': shadowsocks_port, 'method': shadowsocks_method, 'fast_open': shadowsocks_fast_open, 'reuse_port': shadowsocks_reuse_port, 'no_delay': shadowsocks_no_delay, 'mptcp': shadowsocks_mptcp, 'ebpf': shadowsocks_ebpf, 'obfs': shadowsocks_obfs, 'obfs_plugin': shadowsocks_obfs_plugin, 'obfs_type': shadowsocks_obfs_type}, 'glorytun': {'key': glorytun_key, 'udp': {'host_ip': glorytun_udp_host_ip, 'client_ip': glorytun_udp_client_ip}, 'tcp': {'host_ip': glorytun_tcp_host_ip, 'client_ip': glorytun_tcp_client_ip}, 'port': glorytun_port, 'chacha': glorytun_chacha}, 'dsvpn': {'key': dsvpn_key, 'host_ip': dsvpn_host_ip, 'client_ip': dsvpn_client_ip, 'port': dsvpn_port}, 'openvpn': {'key': openvpn_key, 'client_key': openvpn_client_key, 'client_crt': openvpn_client_crt, 'client_ca': openvpn_client_ca, 'host_ip': openvpn_host_ip, 'client_ip': openvpn_client_ip, 'port': openvpn_port, 'cipher': openvpn_cipher},'wireguard': {'key': wireguard_key, 'host_ip': wireguard_host_ip, 'port': wireguard_port, 'client_key': wireguard_client_key, 'client_ip': wireguard_client_ip, 'client_port': wireguard_client_port}, 'mqvpn': {'key': mqvpn_key, 'host_ip': mqvpn_host_ip, 'client_ip': mqvpn_client_ip, 'port': mqvpn_port, 'scheduler': mqvpn_scheduler, 'cc': mqvpn_cc, 'mtu': mqvpn_mtu, 'outer_packet_size': mqvpn_outer_packet_size, 'pmtud': mqvpn_pmtud, 'pmtud_probe_size': mqvpn_pmtud_probe_size, 'log_level': mqvpn_log_level}, 'mqvpn2': {'key': mqvpn2_key, 'host_ip': mqvpn2_host_ip, 'client_ip': mqvpn2_client_ip, 'port': mqvpn2_port, 'scheduler': mqvpn2_scheduler, 'cc': mqvpn2_cc, 'mtu': mqvpn2_mtu, 'init_max_path_id': mqvpn2_init_max_path_id, 'reorder': mqvpn2_reorder, 'log_level': mqvpn2_log_level}, 'shorewall': {'redirect_ports': shorewall_redirect}, 'mptcp': {'enabled': mptcp_enabled, 'checksum': mptcp_checksum, 'path_manager': mptcp_path_manager, 'scheduler': mptcp_scheduler, 'syn_retries': mptcp_syn_retries, 'version': mptcp_version, 'nanbbr_aggressiveness': nanbbr_aggressiveness, 'nanbbr_aggressiveness_capable': nanbbr_aggressiveness_capable, 'nanbbr_aggressiveness_min': NANBBR_AGGRESSIVENESS_MIN, 'nanbbr_aggressiveness_max': NANBBR_AGGRESSIVENESS_MAX, 'nanbbr_var_capabilities': nanbbr_var_capabilities}, 'network': {'congestion_control': congestion_control, 'ipv6_network': ipv6_network, 'ipv6': ipv6_addr, 'ipv4': ipv4_addr, 'domain': vps_domain, 'internet': internet}, 'vpn': {'available': available_vpn, 'current': vpn, 'remoteip': vpn_remote_ip, 'localip': vpn_local_ip, 'rx': vpn_traffic_rx, 'tx': vpn_traffic_tx}, 'iperf': {'user': PRIMARY_ROUTER_USERNAME, 'password': PRIMARY_ROUTER_USERNAME, 'key': iperf3_key}, 'user': {'name': username, 'permission': user_permissions}, 'ip6in4': {'localip': localip6, 'remoteip': remoteip6, 'ula': ula}, 'gre_tunnel': {'enabled': gre_tunnel, 'config': gre_tunnel_conf}, 'v2ray': {'enabled': v2ray, 'config': v2ray_conf, 'tx': v2ray_tx, 'rx': v2ray_rx},'xray': {'enabled': xray, 'config': xray_conf, 'tx': xray_tx, 'rx': xray_rx},'shadowsocks_go': {'enabled': shadowsocks_go, 'config': shadowsocks_go_conf,'tx': ss_go_tx, 'rx': ss_go_rx}, 'proxy': {'available': available_proxy, 'current': proxy}, 'softethervpn': {'enabled': softether, 'port': softether_port, 'password': softether_password, 'cipher': softether_cipher, 'host_ip': softether_host_ip, 'client_ip': softether_client_ip},'localvpn': localvpn}

# Set shadowsocks config
class OBFSPLUGIN(str, Enum):
    v2ray = "v2ray"
    obfs = "obfs"

class OBFSTYPE(str, Enum):
    tls = "tls"
    http = "http"


class ShadowsocksConfigparams(BaseModel):
    port: int = Query(..., gt=0, lt=65535)
    method: str
    fast_open: bool
    reuse_port: bool
    no_delay: bool
    mptcp: bool = Query(True, title="Enable/Disable MPTCP support")
    obfs: bool = Query(False, title="Enable/Disable obfuscation support")
    obfs_plugin: OBFSPLUGIN = Query("v2ray", title="Choose obfuscation plugin")
    obfs_type: OBFSTYPE = Query("tls", title="Choose obfuscation method")
    key: str

@app.post('/shadowsocks', summary="Modify Shadowsocks-libev configuration")
def shadowsocks(*, params: ShadowsocksConfigparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'shadowsocks'}
    if not os.path.isfile('/etc/shadowsocks-libev/manager.json'):
        return {'result': 'warning', 'reason': 'Shadowsocks-lib not installed', 'route': 'shadowsocks'}

    ipv6_network = os.popen('ip -6 addr show ' + IFACE6 +' | grep -oP "(?<=inet6 ).*(?= scope global)"').read().rstrip()
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-libev/manager.json', 'rb'))).hexdigest()
    with open('/etc/shadowsocks-libev/manager.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    try:
        data = json.loads(content)
    except ValueError as e:
        data = {'timeout': 600, 'verbose': 0, 'prefer_ipv6': False}
    #key = data["key"]
    if 'timeout' in data:
        timeout = data["timeout"]
    else:
        timeout = 600
    if 'verbose' in data:
        verbose = data["verbose"]
    else:
        verbose = 0
    prefer_ipv6 = data["prefer_ipv6"]
    port = params.port
    method = params.method
    fast_open = params.fast_open
    reuse_port = params.reuse_port
    no_delay = params.no_delay
    mptcp = params.mptcp
    obfs = params.obfs
    obfs_plugin = params.obfs_plugin
    obfs_type = params.obfs_type
    ebpf = 0
    key = params.key
    if 'port_key' in data:
        portkey = data["port_key"]
        portkey[str(port)] = key
    if 'port_conf' in data:
        portconf = data["port_conf"]
        portconf[str(port)]['key'] = key
    LOG.debug("modif_config_user for shadowsocks_port")
    modif_config_user(PRIMARY_ROUTER_USERNAME, {'shadowsocks_port': port})
    userid = 0
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}

    #ipv4_addr = os.popen('wget -4 -qO- -T 2 http://ip.openmptcprouter.com').read().rstrip()
    if 'hostname' in omr_config_data:
        vps_domain = omr_config_data['hostname']
    else:
        vps_domain = os.popen('wget -4 -qO- -t 1 -T 1 http://hostname.openmptcprouter.com').read().rstrip()
        if vps_domain != '':
            set_global_param('hostname', vps_domain)

    if port is None or method is None or fast_open is None or reuse_port is None or no_delay is None or key is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'shadowsocks'}
    if 'port_key' in data:
        if ipv6_network == '':
            if obfs:
                if obfs_plugin == "v2ray":
                    if obfs_type == "tls":
                        if vps_domain == '':
                            shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls'}
                        else:
                            shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server'}
                else:
                    if obfs_type == 'tls':
                        if vps_domain == '':
                            shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400'}
                        else:
                            shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=http;mptcp;fast-open;t=400'}
            else:
                shadowsocks_config = {'server': '0.0.0.0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl'}
        else:
            if obfs:
                if obfs_plugin == "v2ray":
                    if obfs_type == "tls":
                        if vps_domain == '':
                            shadowsocks_config = {'server': '::0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls'}
                        else:
                            shadowsocks_config = {'server': '::0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '::0', 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server'}
                else:
                    if obfs_type == 'tls':
                        if vps_domain == '':
                            shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400'}
                        else:
                            shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=http;mptcp;fast-open;t=400'}
            else:
                shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_key': portkey, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl'}
    else:
        if ipv6_network == '':
            if obfs:
                if obfs_plugin == "v2ray":
                    if obfs_type == "tls":
                        if vps_domain == '':
                            shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls'}
                        else:
                            shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server'}
                else:
                    if obfs_type == 'tls':
                        if vps_domain == '':
                            shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400'}
                        else:
                            shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=http;mptcp;fast-open;t=400'}
            else:
                shadowsocks_config = {'server': '0.0.0.0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl'}
        else:
            if obfs:
                if obfs_plugin == "v2ray":
                    if obfs_type == "tls":
                        if vps_domain == '':
                            shadowsocks_config = {'server': '::0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls'}
                        else:
                            shadowsocks_config = {'server': '::0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server;tls;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': '::0', 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/v2ray-plugin', 'plugin_opts': 'server'}
                else:
                    if obfs_type == 'tls':
                        if vps_domain == '':
                            shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400'}
                        else:
                            shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=tls;mptcp;fast-open;t=400;host=' + vps_domain}
                    else:
                        shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl', 'plugin': '/usr/local/bin/obfs-server', 'plugin_opts': 'obfs=http;mptcp;fast-open;t=400'}
            else:
                shadowsocks_config = {'server': ('[::0]', '0.0.0.0'), 'port_conf': portconf, 'local_port': 1081, 'mode': 'tcp_and_udp', 'timeout': timeout, 'method': method, 'verbose': verbose, 'ipv6_first': True, 'prefer_ipv6': prefer_ipv6, 'fast_open': fast_open, 'no_delay': no_delay, 'reuse_port': reuse_port, 'mptcp': mptcp, 'ebpf': ebpf, 'acl': '/etc/shadowsocks-libev/local.acl'}

    with open('/etc/shadowsocks-libev/manager.json', 'w') as outfile:
        json.dump(shadowsocks_config, outfile, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-libev/manager.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart shadowsocks-libev-manager@manager.service")
        #for x in range(1, os.cpu_count()):
        #    os.system("systemctl restart shadowsocks-libev-manager@manager" + str(x) + ".service")
        router_user = get_primary_router_user()
        shorewall_add_port(router_user, str(port), 'tcp', 'shadowsocks')
        shorewall_add_port(router_user, str(port), 'udp', 'shadowsocks')
        #set_lastchange()
        return {'result': 'done', 'reason': 'changes applied', 'route': 'shadowsocks'}
    else:
        return {'result': 'done', 'reason': 'no changes', 'route': 'shadowsocks'}

class ShadowsocksGoConfigparams(BaseModel):
    port: int = Query(..., gt=0, lt=65535)
    method: str
    fast_open: bool
    reuse_port: bool
    mptcp: bool = Query(True, title="Enable/Disable MPTCP support")
    #key: str

@app.post('/shadowsocks-go', summary="Modify Shadowsocks-Go configuration")
def shadowsocks_go(*, params: ShadowsocksGoConfigparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'shadowsocks-go'}
    if not os.path.isfile('/etc/shadowsocks-go/server.json'):
        return {'result': 'warning', 'reason': 'Shadowsocks-go not installed', 'route': 'shadowsocks-go'}

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-go/server.json', 'rb'))).hexdigest()
    with open('/etc/shadowsocks-go/server.json') as f:
        content = f.read()
    content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
    try:
        data = json.loads(content)
    except ValueError as e:
        return {'result': 'error', 'reason': 'Read only user', 'route': 'shadowsocks-go'}
    port = params.port
    # If method is aes 128 then key need to be length 16 instead of 32, so force aes-256-gcm for now
    method = params.method
    if method == "2022-blake3-aes-128-gcm":
        method = "2022-blake3-aes-256-gcm"
    fast_open = params.fast_open
    reuse_port = params.reuse_port
    mptcp = params.mptcp
    #key = params.key
    LOG.debug("modif_config_user for shadowsocks-go port")
    shadowsocks_go_psk = os.popen("jq -r '.servers[] | select(.name==" + '"ss-2022"' + ") | .psk' /etc/shadowsocks-go/server.json").read().rstrip()
    shadowsocks_go_upsk = os.popen("jq -r --arg user " + '"' + PRIMARY_ROUTER_USERNAME + '"' + " '.[$user]' /etc/shadowsocks-go/upsks.json").read().rstrip()
    shadowsocks_go_conf= { 'password': shadowsocks_go_psk + ':' + shadowsocks_go_upsk, 'port': port, 'protocol': method }
    modif_config_user(PRIMARY_ROUTER_USERNAME, {'shadowsocks-go': shadowsocks_go_conf})

    modif_config_user(PRIMARY_ROUTER_USERNAME, {'shadowsocks-go': {'port': port,'method': method}})
    userid = 0
    data["servers"][0]["tcpListeners"][0]["address"] = ":" + str(port)
    data["servers"][0]["tcpListeners"][0]["fastOpen"] = fast_open
    data["servers"][0]["listenerTFO"] = fast_open
    data["servers"][0]["tcpListeners"][0]["reusePort"] = reuse_port
    data["servers"][0]["tcpListeners"][0]["multipath"] = mptcp
    data["servers"][0]["protocol"] = method
    #data.servers[0].psk = key
    with open('/etc/shadowsocks-go/server.json', 'w') as outfile:
        json.dump(data, outfile, indent=4)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-go/server.json', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart shadowsocks-go.service")
        router_user = get_primary_router_user()
        shorewall_add_port(router_user, str(port), 'tcp', 'shadowsocks-go')
        shorewall_add_port(router_user, str(port), 'udp', 'shadowsocks-go')
        #set_lastchange()
        return {'result': 'done', 'reason': 'changes applied', 'route': 'shadowsocks-go'}
    else:
        return {'result': 'done', 'reason': 'no changes', 'route': 'shadowsocks-go'}

# Set shorewall config
class IPPROTO(str, Enum):
    ipv4 = "ipv4"
    ipv6 = "ipv6"

class ShorewallAllparams(BaseModel):
    redirect_ports: str = Query(..., title="Port or ports range")
    ipproto: IPPROTO = Query("ipv4", title="Protocol IP to apply changes")

@app.post('/shorewall', summary="Redirect all ports from Server to router")
def shorewall(*, params: ShorewallAllparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'shorewall'}
    state = params.redirect_ports
    if state is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'shorewall'}
    if params.ipproto == 'ipv4':
        initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
        fd, tmpfile = mkstemp()
        with open('/etc/shorewall/rules', 'r') as f, open(tmpfile, 'a+') as n:
            for line in f:
                if state == 'enable' and line == '#DNAT		net		vpn:$OMR_ADDR	tcp	1-64999\n':
                    n.write(line.replace(line[:1], ''))
                elif state == 'enable' and line == '#DNAT		net		vpn:$OMR_ADDR	udp	1-64999\n':
                    n.write(line.replace(line[:1], ''))
                elif state == 'disable' and line == 'DNAT		net		vpn:$OMR_ADDR	tcp	1-64999\n':
                    n.write('#' + line)
                elif state == 'disable' and line == 'DNAT		net		vpn:$OMR_ADDR	udp	1-64999\n':
                    n.write('#' + line)
                else:
                    n.write(line)
        os.close(fd)
        move(tmpfile, '/etc/shorewall/rules')
        final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/rules', 'rb'))).hexdigest()
        if initial_md5 != final_md5:
            os.system("systemctl -q reload shorewall")
    else:
        initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
        fd, tmpfile = mkstemp()
        with open('/etc/shorewall6/rules', 'r') as f, open(tmpfile, 'a+') as n:
            for line in f:
                if state == 'enable' and line == '#DNAT		net		vpn:$OMR_ADDR	tcp	1-64999\n':
                    n.write(line.replace(line[:1], ''))
                elif state == 'enable' and line == '#DNAT		net		vpn:$OMR_ADDR	udp	1-64999\n':
                    n.write(line.replace(line[:1], ''))
                elif state == 'disable' and line == 'DNAT		net		vpn:$OMR_ADDR	tcp	1-64999\n':
                    n.write('#' + line)
                elif state == 'disable' and line == 'DNAT		net		vpn:$OMR_ADDR	udp	1-64999\n':
                    n.write('#' + line)
                else:
                    n.write(line)
        os.close(fd)
        move(tmpfile, '/etc/shorewall6/rules')
        final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/rules', 'rb'))).hexdigest()
        if initial_md5 != final_md5:
            os.system("systemctl -q reload shorewall6")
    # Need to do the same for IPv6...
    return {'result': 'done', 'reason': 'changes applied'}

class ShorewallListparams(BaseModel):
    name: str
    ipproto: IPPROTO = Query("ipv4", title="Protocol IP to list")

@app.post('/shorewalllist', summary="Display all OpenMPTCProuter rules in Shorewall config")
def shorewall_list(*, params: ShorewallListparams, current_user: User = Depends(get_current_user)):
    name = params.name
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'shorewalllist'}
    fwlist = []
    if params.ipproto == 'ipv4':
        with open('/etc/shorewall/rules', 'r') as f:
            for line in f:
                if '# OMR ' + PRIMARY_ROUTER_USERNAME + ' ' + name in line:
                    fwlist.append(line)
    else:
        with open('/etc/shorewall6/rules', 'r') as f:
            for line in f:
                if '# OMR ' + PRIMARY_ROUTER_USERNAME + ' ' + name in line:
                    fwlist.append(line)
    return {'list': fwlist}

class Shorewallparams(BaseModel):
    name: str
    port: str
    proto: str
    fwtype: str
    ipproto: IPPROTO = Query("ipv4", title="Protocol IP for changes")
    source_dip: str = ""
    source_ip: str = ""
    dest_port: str = ""
    comment: str = ""

@app.post('/shorewallopen', summary="Redirect a port from Server to Router")
def shorewall_open(*, params: Shorewallparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'shorewallopen'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    name = params.name
    port = params.port
    proto = params.proto
    fwtype = params.fwtype
    source_dip = params.source_dip
    source_ip = params.source_ip
    dest_port = params.dest_port
    comment = params.comment
    if comment != '':
        comment = ' --- ' + comment
    vpn = "default"
    username = PRIMARY_ROUTER_USERNAME
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'shorewallopen'}
    #proxy = 'shadowsocks'
    #if 'proxy' in omr_config_data['users'][0][username]:
    #    proxy = omr_config_data['users'][0][username]['proxy']
    if params.ipproto == 'ipv4':
        if 'gre_tunnels' in omr_config_data['users'][0][PRIMARY_ROUTER_USERNAME]:
            for tunnel in omr_config_data['users'][0][PRIMARY_ROUTER_USERNAME]['gre_tunnels']:
                if omr_config_data['users'][0][PRIMARY_ROUTER_USERNAME]['gre_tunnels'][tunnel]['public_ip'] == source_dip:
                    vpn = omr_config_data['users'][0][PRIMARY_ROUTER_USERNAME]['gre_tunnels'][tunnel]['remote_ip']
        shorewall_add_port(get_primary_router_user(), str(port), proto, name, fwtype, source_dip, source_ip, vpn, comment, dest_port)
    else:
        shorewall6_add_port(get_primary_router_user(), str(port), proto, name, fwtype, source_dip, source_ip, comment, dest_port)
    return {'result': 'done', 'reason': 'changes applied'}

@app.post('/shorewallclose', summary="Remove a redirected port")
def shorewall_close(*, params: Shorewallparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'shorewallclose'}
    name = params.name
    port = params.port
    proto = params.proto
    fwtype = params.fwtype
    source_dip = params.source_dip
    source_ip = params.source_ip
    comment = params.comment
    if comment != '':
        comment = ' --- ' + comment
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'shorewallclose'}
    if params.ipproto == 'ipv4':
        shorewall_del_port(PRIMARY_ROUTER_USERNAME, str(port), proto, name, 'DNAT', source_dip, source_ip, comment)
        shorewall_del_port(PRIMARY_ROUTER_USERNAME, str(port), proto, name, 'ACCEPT', source_dip, source_ip, comment)
    else:
        shorewall6_del_port(PRIMARY_ROUTER_USERNAME, str(port), proto, name, 'DNAT', source_dip, source_ip, comment)
        shorewall6_del_port(PRIMARY_ROUTER_USERNAME, str(port), proto, name, 'ACCEPT', source_dip, source_ip, comment)
    return {'result': 'done', 'reason': 'changes applied', 'route': 'shorewallclose'}

class SipALGparams(BaseModel):
    enable: bool = Query(True, title="Enable or disable SIP ALG")

@app.post('/sipalg', summary="Enable/Disable SIP ALG")
def sipalg(*, params: SipALGparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'sipalg'}
    enable = params.enable

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/shorewall.conf', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/shorewall/shorewall.conf', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if not enable and line == 'DONT_LOAD=\n':
                n.write('DONT_LOAD=nf_conntrack_sip\n')
            elif not enable and line == 'AUTOHELPERS=Yes\n':
                n.write('AUTOHELPERS=No\n')
            elif enable and 'DONT_LOAD' in line and line != 'DONT_LOAD=\n':
                n.write('DONT_LOAD=\n')
            elif enable and line == 'AUTOHELPERS=No\n':
                n.write('AUTOHELPERS=Yes\n')
            else:
                n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/shorewall/shorewall.conf')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/shorewall.conf', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall")
    return {'result': 'done', 'reason': 'changes applied', 'route': 'sipalg'}

class V2rayconfig(BaseModel):
    pass

@app.post('/v2ray', summary="Set v2ray settings")
def v2ray(*, params: V2rayconfig, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'v2ray'}
    if not os.path.isfile('/etc/v2ray/v2ray-server.json'):
        return {'result': 'warning', 'reason': 'V2Ray not installed', 'route': 'v2ray'}

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    username = PRIMARY_ROUTER_USERNAME
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/v2ray/v2ray-server.json', 'rb'))).hexdigest()
    v2ray_key = os.popen("jq -r '.inbounds[0].settings.clients[] | select(.email==" + '"' + username + '"' + ") | .id' /etc/v2ray/v2ray-server.json").read().rstrip()
    v2ray_port = os.popen('jq -r .inbounds[0].port /etc/v2ray/v2ray-server.json').read().rstrip()
    v2ray_conf = { 'key': v2ray_key, 'port': v2ray_port}
    LOG.debug("modif_config_user for v2ray conf")
    modif_config_user(username, {'v2ray': v2ray_conf})
    if initial_md5 != final_md5:
        os.system("systemctl -q restart v2ray")
        #set_lastchange()
        return {'result': 'done', 'reason': 'changes applied', 'route': 'v2ray'}
    else:
        return {'result': 'done', 'reason': 'no changes', 'route': 'v2ray'}

class XRAYTRANSPORT(str, Enum):
    tcp = "tcp"
    grpc = "grpc"
    xhttp = "xhttp"

class Xrayconfig(BaseModel):
    vless_reality: bool = Query(False, title="Enable or disable VLESS Reality")
    ss_method: str = "2022-blake3-aes-256-gcm"
    transport: XRAYTRANSPORT = Query("tcp", title="Choose transport")

@app.post('/xray', summary="Set xray settings")
def xray(*, params: Xrayconfig, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'xray'}
    if not os.path.isfile('/etc/xray/xray-server.json'):
        return {'result': 'warning', 'reason': 'Xay not installed', 'route': 'xray'}

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    test_vless_reality = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-vless-reality' + '"' + ")' /etc/xray/xray-server.json").read().rstrip()
    if test_vless_reality != '':
        chk_vless_reality = True
    else:
        chk_vless_reality = False
    with open('/etc/xray/xray-server.json') as f:
        xray_config = json.load(f)
        if params.vless_reality and not chk_vless_reality:
            with open('/etc/xray/xray-vless-reality.json') as f:
                vless_reality_config = json.load(f)
            xray_config['inbounds'].append(vless_reality_config['inbounds'][0])
        elif not params.vless_reality and chk_vless_reality:
            for inbounds in xray_config['inbounds']:
                if inbounds['tag'] == 'omrin-vless-reality':
                    xray_config['inbounds'].remove(inbounds)
        for inbounds in xray_config['inbounds']:
            if inbounds.get('tag', '').startswith('omr-rpf-'):
                continue
            if inbounds['tag'] == 'omrin-shadowsocks-tunnel':
                inbounds['settings']['method'] = params.ss_method
            if 'streamSettings' in inbounds:
                inbounds['streamSettings']['network'] = params.transport

    with open('/etc/xray/xray-server.json', 'w') as outfile:
        json.dump(xray_config, outfile, indent=4)
    username = PRIMARY_ROUTER_USERNAME
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/xray/xray-server.json', 'rb'))).hexdigest()
    xray_key = os.popen("jq -r '.inbounds[0].settings.clients[] | select(.email==" + '"' + username + '"' + ") | .id' /etc/xray/xray-server.json").read().rstrip()
    xray_ss_skey = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-shadowsocks-tunnel' + '"' + ") | .settings.password' /etc/xray/xray-server.json").read().rstrip()
    xray_ss_ukey = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-shadowsocks-tunnel' + '"' + ") | .settings.clients[] | select(.email==" + '"' + username + '"' + ") | .password' /etc/xray/xray-server.json").read().rstrip()
    xray_ss_key = xray_ss_skey + ':' + xray_ss_ukey
    xray_port = os.popen('jq -r .inbounds[0].port /etc/xray/xray-server.json').read().rstrip()
    test_vless_reality = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-vless-reality' + '"' + ")' /etc/xray/xray-server.json").read().rstrip()
    if test_vless_reality != '':
        vless_reality = True
    else:
        vless_reality = False
    if os.path.isfile('/etc/xray/xray-vless-reality.json'):
        xray_vless_reality_public_key = os.popen("jq -r '.inbounds[] | select(.tag==" + '"' + 'omrin-vless-reality' + '"' + ") | .streamSettings.realitySettings.publicKey' /etc/xray/xray-vless-reality.json").read().rstrip()
        xray_conf = { 'key': xray_key, 'port': xray_port, 'sskey': xray_ss_key, 'vless_reality_key': xray_vless_reality_public_key, 'vless_reality': vless_reality, 'ss_method': params.ss_method }
        LOG.debug("modif_config_user for xray conf")
        modif_config_user(username, {'xray': xray_conf})
    if initial_md5 != final_md5:
        if params.vless_reality and not chk_vless_reality:
            shorewall_add_port(get_primary_router_user(), '443', 'tcp', 'xray vless-reality')
        elif not params.vless_reality and chk_vless_reality:
            shorewall_del_port(PRIMARY_ROUTER_USERNAME, '443', 'tcp', 'xray vless-reality')
        os.system("systemctl -q restart xray")
        #set_lastchange()
        return {'result': 'done', 'reason': 'changes applied', 'route': 'xray'}
    else:
        return {'result': 'done', 'reason': 'no changes', 'route': 'xray'}


class V2rayparams(BaseModel):
    name: str
    port: str
    proto: str
    destip: str = ""
    destport: str = ""

@app.post('/v2rayredirect', summary="Redirect a port from Server to Router with V2Ray")
def v2ray_redirect(*, params: V2rayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'v2rayredirect'}
    if not os.path.isfile('/etc/v2ray/v2ray-server.json'):
        return {'result': 'warning', 'reason': 'V2Ray not installed', 'route': 'v2rayredirect'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    username = PRIMARY_ROUTER_USERNAME
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'v2rayredirect'}
    v2ray_add_port(get_primary_router_user(), port, proto, name, destip, destport)
    return {'result': 'done', 'reason': 'changes applied'}

class Xrayparams(BaseModel):
    name: str
    port: str
    proto: str
    destip: str = ""
    destport: str = ""

@app.post('/xrayredirect', summary="Redirect a port from Server to Router with XRay")
def xray_redirect(*, params: Xrayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'xrayredirect'}
    if not os.path.isfile('/etc/xray/xray-server.json'):
        return {'result': 'warning', 'reason': 'Xay not installed', 'route': 'xrayredirect'}

    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    username = PRIMARY_ROUTER_USERNAME
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'xrayredirect'}
    xray_add_port(get_primary_router_user(), port, proto, name, destip, destport)
    return {'result': 'done', 'reason': 'changes applied'}

@app.post('/xrayrpfredirect', summary="Redirect a TCP port from Server to Router with XRay reverse")
def xray_rpf_redirect(*, params: Xrayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'xrayrpfredirect'}
    if not os.path.isfile('/etc/xray/xray-server.json'):
        return {'result': 'warning', 'reason': 'XRay not installed', 'route': 'xrayrpfredirect'}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'xrayrpfredirect'}
    return xray_rpf_add_port(get_primary_router_user(), port, proto, name, destip, destport)

@app.post('/v2rayunredirect', summary="Remove a redirected port from Server to Router with V2Ray")
def v2ray_unredirect(*, params: V2rayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'v2rayunredirect'}
    if not os.path.isfile('/etc/v2ray/v2ray-server.json'):
        return {'result': 'warning', 'reason': 'V2Ray not installed', 'route': 'v2rayunredirect'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    username = PRIMARY_ROUTER_USERNAME
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'v2rayunredirect'}
    v2ray_del_port(get_primary_router_user(), port, proto, name, destip, destport)
    return {'result': 'done', 'reason': 'changes applied'}

@app.post('/xrayunredirect', summary="Remove a redirected port from Server to Router with XRay")
def xray_unredirect(*, params: Xrayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'xrayunredirect'}
    if not os.path.isfile('/etc/xray/xray-server.json'):
        return {'result': 'warning', 'reason': 'Xay not installed', 'route': 'xrayunredirect'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        try:
            omr_config_data = json.load(f)
        except ValueError as e:
            omr_config_data = {}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    username = PRIMARY_ROUTER_USERNAME
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'xrayunredirect'}
    xray_del_port(get_primary_router_user(), port, proto, name, destip, destport)
    return {'result': 'done', 'reason': 'changes applied'}

@app.post('/xrayrpfunredirect', summary="Remove an XRay reverse redirected port")
def xray_rpf_unredirect(*, params: Xrayparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'xrayrpfunredirect'}
    if not os.path.isfile('/etc/xray/xray-server.json'):
        return {'result': 'warning', 'reason': 'XRay not installed', 'route': 'xrayrpfunredirect'}
    name = params.name
    port = params.port
    proto = params.proto
    destip = params.destip
    destport = params.destport
    if name is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'xrayrpfunredirect'}
    return xray_rpf_del_port(get_primary_router_user(), port, proto, name, destip, destport)

# Set MPTCP config
class MPTCPparams(BaseModel):
    checksum: str
    path_manager: str
    scheduler: str
    syn_retries: int
    congestion_control: str
    version: int = 0
    nanbbr_aggressiveness: Optional[int] = Query(
        None,
        ge=NANBBR_AGGRESSIVENESS_MIN,
        le=NANBBR_AGGRESSIVENESS_MAX,
    )

@app.post('/mptcp', summary="Modify MPTCP configuration of the server")
def mptcp(*, params: MPTCPparams, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'mptcp'}
    checksum = params.checksum
    path_manager = params.path_manager
    scheduler = params.scheduler
    syn_retries = params.syn_retries
    congestion_control = params.congestion_control
    version = params.version
    nanbbr_aggressiveness = params.nanbbr_aggressiveness
    if not checksum or not path_manager or not scheduler or not syn_retries or not congestion_control:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'mptcp'}
    if checksum not in ['0', '1'] or not 1 <= syn_retries <= 255 or version not in [0, 1]:
        return {'result': 'error', 'reason': 'Invalid MPTCP numeric parameters', 'route': 'mptcp'}
    safe_name = re.compile(r'^[A-Za-z0-9_.-]+$')
    if not safe_name.fullmatch(path_manager) or not safe_name.fullmatch(scheduler) or not safe_name.fullmatch(congestion_control):
        return {'result': 'error', 'reason': 'Invalid MPTCP setting name', 'route': 'mptcp'}
    if congestion_control in NANBBR_VAR_MODULES and nanbbr_aggressiveness is None:
        return {
            'result': 'error',
            'reason': 'nanbbr_aggressiveness is required for NanBBR var',
            'route': 'mptcp',
        }

    os.makedirs(path.dirname(MPTCP_LOCK_FILE), exist_ok=True)
    with open(MPTCP_LOCK_FILE, 'a+', encoding='ascii') as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        nanbbr_parameters = {}
        if nanbbr_aggressiveness is not None:
            for nanbbr_cc in NANBBR_VAR_MODULES:
                try:
                    nanbbr_parameters[nanbbr_cc] = ensure_nanbbr_parameter(nanbbr_cc)
                except RuntimeError:
                    if nanbbr_cc == congestion_control:
                        return {
                            'result': 'error',
                            'reason': 'NanBBR var aggressiveness is not supported',
                            'route': 'mptcp',
                        }
            if not nanbbr_parameters:
                return {
                    'result': 'error',
                    'reason': 'NanBBR var aggressiveness is not supported',
                    'route': 'mptcp',
                }

        try:
            with open('/proc/sys/net/ipv4/tcp_available_congestion_control') as cc_file:
                available_cc = cc_file.read().split()
        except OSError:
            available_cc = []
        if available_cc and congestion_control not in available_cc:
            return {'result': 'error', 'reason': 'Congestion control is not available', 'route': 'mptcp'}

        sysctl_values = []
        if path.exists('/proc/sys/net/mptcp/mptcp_enabled'):
            sysctl_values.extend([
                ('net.mptcp.mptcp_checksum', checksum),
                ('net.mptcp.mptcp_path_manager', path_manager),
                ('net.mptcp.mptcp_scheduler', scheduler),
                ('net.mptcp.mptcp_syn_retries', syn_retries),
                ('net.mptcp.mptcp_version', version),
            ])
        else:
            sysctl_values.append(('net.mptcp.checksum_enabled', checksum))
        sysctl_values.append(('net.ipv4.tcp_congestion_control', congestion_control))

        old_sysctl_values = {}
        old_nanbbr_values = {}
        applied_sysctls = []
        applied_nanbbr_parameters = []
        restored_files = []
        shadowsocks_file = '/etc/sysctl.d/90-shadowsocks.conf'
        try:
            with open(shadowsocks_file, 'rb') as config_file:
                old_shadowsocks_content = config_file.read()
            try:
                with open(NANBBR_CONFIG_FILE, 'rb') as config_file:
                    old_nanbbr_content = config_file.read()
            except FileNotFoundError:
                old_nanbbr_content = None

            for key, unused_value in sysctl_values:
                result = subprocess.run(
                    ['sysctl', '-n', key],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                old_sysctl_values[key] = result.stdout.strip()
            for parameter in nanbbr_parameters.values():
                with open(parameter, 'r') as parameter_file:
                    old_nanbbr_values[parameter] = parameter_file.read().strip()

            old_lines = old_shadowsocks_content.decode('utf-8').splitlines(keepends=True)
            new_lines = [
                line for line in old_lines
                if 'net.mptcp' not in line and 'net.ipv4.tcp_congestion_control' not in line
            ]
            new_lines.extend([
                'net.mptcp.mptcp_checksum=' + checksum + "\n",
                'net.mptcp.mptcp_path_manager=' + path_manager + "\n",
                'net.mptcp.mptcp_scheduler=' + scheduler + "\n",
                'net.mptcp.mptcp_syn_retries=' + str(syn_retries) + "\n",
                'net.mptcp.mptcp_version=' + str(version) + "\n",
                'net.mptcp.checksum_enabled=' + checksum + "\n",
                'net.ipv4.tcp_congestion_control=' + congestion_control + "\n",
            ])
            new_shadowsocks_content = ''.join(new_lines).encode('utf-8')

            for key, value in sysctl_values[:-1]:
                applied_sysctls.append(key)
                subprocess.run(
                    ['sysctl', '-qw', key + '=' + str(value)],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                readback = subprocess.run(
                    ['sysctl', '-n', key],
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout.strip()
                if readback != str(value):
                    raise RuntimeError(key + ' readback mismatch')

            if nanbbr_aggressiveness is not None:
                for parameter in nanbbr_parameters.values():
                    applied_nanbbr_parameters.append(parameter)
                    with open(parameter, 'w') as parameter_file:
                        parameter_file.write(str(nanbbr_aggressiveness))
                    with open(parameter, 'r') as parameter_file:
                        readback = parameter_file.read().strip()
                    if readback != str(nanbbr_aggressiveness):
                        raise RuntimeError(parameter + ' readback mismatch')

            cc_key, cc_value = sysctl_values[-1]
            applied_sysctls.append(cc_key)
            subprocess.run(
                ['sysctl', '-qw', cc_key + '=' + str(cc_value)],
                check=True,
                capture_output=True,
                text=True,
            )
            readback = subprocess.run(
                ['sysctl', '-n', cc_key],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
            if readback != str(cc_value):
                raise RuntimeError(cc_key + ' readback mismatch')

            if nanbbr_aggressiveness is not None:
                new_nanbbr_content = nanbbr_config_content(nanbbr_aggressiveness)
                if old_nanbbr_content != new_nanbbr_content:
                    restored_files.append(NANBBR_CONFIG_FILE)
                    atomic_write_file(NANBBR_CONFIG_FILE, new_nanbbr_content)
            if old_shadowsocks_content != new_shadowsocks_content:
                restored_files.append(shadowsocks_file)
                atomic_write_file(shadowsocks_file, new_shadowsocks_content)
        except (OSError, UnicodeError, subprocess.SubprocessError, RuntimeError) as error:
            rollback_errors = []
            for key in reversed(applied_sysctls):
                try:
                    subprocess.run(
                        ['sysctl', '-qw', key + '=' + old_sysctl_values[key]],
                        check=True,
                        capture_output=True,
                        text=True,
                    )
                    restored_value = subprocess.run(
                        ['sysctl', '-n', key],
                        check=True,
                        capture_output=True,
                        text=True,
                    ).stdout.strip()
                    if restored_value != old_sysctl_values[key]:
                        rollback_errors.append(key + ' rollback readback mismatch')
                except (OSError, subprocess.SubprocessError) as rollback_error:
                    rollback_errors.append(str(rollback_error))
            for parameter in reversed(applied_nanbbr_parameters):
                try:
                    with open(parameter, 'w') as parameter_file:
                        parameter_file.write(old_nanbbr_values[parameter])
                    with open(parameter, 'r') as parameter_file:
                        restored_value = parameter_file.read().strip()
                    if restored_value != old_nanbbr_values[parameter]:
                        rollback_errors.append(parameter + ' rollback readback mismatch')
                except OSError as rollback_error:
                    rollback_errors.append(str(rollback_error))
            if shadowsocks_file in restored_files:
                try:
                    atomic_write_file(shadowsocks_file, old_shadowsocks_content)
                except OSError as rollback_error:
                    rollback_errors.append(str(rollback_error))
            if NANBBR_CONFIG_FILE in restored_files:
                try:
                    if old_nanbbr_content is None:
                        try:
                            os.remove(NANBBR_CONFIG_FILE)
                        except FileNotFoundError:
                            pass
                    else:
                        atomic_write_file(NANBBR_CONFIG_FILE, old_nanbbr_content)
                except OSError as rollback_error:
                    rollback_errors.append(str(rollback_error))
            reason = 'Unable to apply MPTCP configuration: ' + str(error)
            if rollback_errors:
                reason += '; rollback incomplete'
            LOG.error(reason)
            return {'result': 'error', 'reason': reason, 'route': 'mptcp'}

    if old_shadowsocks_content != new_shadowsocks_content:
        if os.path.isfile('/etc/shadowsocks-libev/manager.json'):
            os.system("systemctl -q restart shadowsocks-libev-manager@manager")
        if os.path.isfile('/etc/v2ray/v2ray-server.json'):
            os.system("systemctl -q restart v2ray")
        if os.path.isfile('/etc/xray/xray-server.json'):
            os.system("systemctl -q restart xray")
        if os.path.isfile('/etc/glorytun-tcp/tun0'):
            os.system("systemctl -q restart glorytun-tcp@tun0")
        if os.path.isfile('/etc/openvpn/tun0.conf'):
            os.system("systemctl -q restart openvpn@tun0")
    #set_lastchange()
    return {'result': 'done', 'reason': 'changes applied'}

class VPN(str, Enum):
    openvpn = "openvpn"
    openvpnbonding = "openvpn_bonding"
    glorytuntcp = "glorytun_tcp"
    glorytunudp = "glorytun_udp"
    dsvpn = "dsvpn"
    mqvpn = "mqvpn"
    mqvpn2 = "mqvpn2"
    softether = "softether"
    none = "none"

class Vpn(BaseModel):
    vpn: VPN

# Set global VPN config
@app.post('/vpn', summary="Set VPN used by the current user")
def vpn(*, vpnconfig: Vpn, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'vpn'}
    vpn = vpnconfig.vpn
    if not vpn:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'vpn'}
    os.system('echo ' + vpn + ' > /etc/openmptcprouter-vps-admin/current-vpn')
    LOG.debug("modif_config_user for vpn setting")
    modif_config_user(PRIMARY_ROUTER_USERNAME, {'vpn': vpn})
    #set_lastchange()
    return {'result': 'done', 'reason': 'changes applied'}

class PROXY(str, Enum):
    v2ray = "v2ray"
    v2rayvless = "v2ray-vless"
    v2rayvmess = "v2ray-vmess"
    v2raysocks = "v2ray-socks"
    v2raytrojan = "v2ray-trojan"
    xray = "xray"
    xrayvless = "xray-vless"
    xrayvmess = "xray-vmess"
    xraysocks = "xray-socks"
    xraytrojan = "xray-trojan"
    xrayshadowsocks = "xray-shadowsocks"
    shadowsockslibev = "shadowsocks"
    shadowsocksgo = "shadowsocks-go"
    shadowsocksrust = "shadowsocks-rust"
    none = "none"

class Proxy(BaseModel):
    proxy: PROXY

# Set global Proxy config
@app.post('/proxy', summary="Set Proxy used by the current user")
def proxy(*, proxyconfig: Proxy, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'proxy'}
    proxy = proxyconfig.proxy
    if not proxy:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'proxy'}
    os.system('echo ' + proxy + ' > /etc/openmptcprouter-vps-admin/current-proxy')
    LOG.debug("modif_config_user for proxy")
    modif_config_user(PRIMARY_ROUTER_USERNAME, {'proxy': proxy})
    #set_lastchange()
    return {'result': 'done', 'reason': 'changes applied'}


class GlorytunConfig(BaseModel):
    key: str
    port: int = Query(..., gt=0, lt=65535, title="Glorytun TCP and UDP port")
    chacha: bool = Query(True, title="Enable of disable chacha20, if disable AES is used")

# Set Glorytun config
@app.post('/glorytun', summary="Modify Glorytun configuration")
def glorytun(*, glorytunconfig: GlorytunConfig, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'glorytun'}
    if not os.path.isfile('/etc/glorytun-tcp/tun0') and not os.path.isfile('/etc/glorytun-udp/tun0'):
        return {'result': 'warning', 'reason': 'Glorytun is not installed', 'route': 'glorytun'}

    userid = 0
    key = glorytunconfig.key
    port = glorytunconfig.port
    chacha = glorytunconfig.chacha
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/glorytun-tcp/tun' + str(userid), 'rb'))).hexdigest()
    with open('/etc/glorytun-tcp/tun' + str(userid) + '.key', 'w') as outfile:
        outfile.write(key)
    with open('/etc/glorytun-udp/tun' + str(userid) + '.key', 'w') as outfile:
        outfile.write(key)
    fd, tmpfile = mkstemp()
    with open('/etc/glorytun-tcp/tun' + str(userid), 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if 'PORT=' in line:
                n.write('PORT=' + str(port) + '\n')
            elif 'OPTIONS=' in line:
                if chacha:
                    n.write('OPTIONS="chacha20 retry count -1 const 5000000 timeout 90000 keepalive count 5 idle 10 interval 2 buffer-size 65536 multiqueue"\n')
                else:
                    n.write('OPTIONS="retry count -1 const 5000000 timeout 90000 keepalive count 5 idle 10 interval 2 buffer-size 65536 multiqueue"\n')
            else:
                n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/glorytun-tcp/tun' + str(userid))
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/glorytun-tcp/tun' + str(userid), 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart glorytun-tcp@tun" + str(userid))
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/glorytun-udp/tun' + str(userid), 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/glorytun-udp/tun' + str(userid), 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if 'BIND_PORT=' in line:
                n.write('BIND_PORT=' + str(port) + '\n')
            elif 'OPTIONS=' in line:
                if chacha:
                    n.write('OPTIONS="chacha persist"\n')
                else:
                    n.write('OPTIONS="persist"\n')
            else:
                n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/glorytun-udp/tun' + str(userid))
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/glorytun-udp/tun' + str(userid), 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart glorytun-udp@tun" + str(userid))
    router_user = get_primary_router_user()
    shorewall_add_port(router_user, str(port), 'tcp', 'glorytun')
    shorewall_add_port(router_user, str(port), 'udp', 'glorytun')
    #set_lastchange()
    return {'result': 'done'}

# Set A Dead Simple VPN config
class DSVPN(BaseModel):
    key: str
    port: int = Query(..., gt=0, lt=65535)

@app.post('/dsvpn', summary="Modify DSVPN configuration")
def dsvpn(*, params: DSVPN, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'dsvpn'}
    if not os.path.isfile('/etc/dsvpn/dsvpn'):
        return {'result': 'warning', 'reason': 'DSVPN is not installed', 'route': 'dsvpn'}
    userid = 0
    key = params.key
    port = params.port
    if not key or port is None:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'dsvpn'}

    fd, tmpfile = mkstemp()
    with open('/etc/dsvpn/dsvpn' + str(userid), 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if 'PORT=' in line:
                n.write('PORT=' + str(port) + '\n')
            else:
                n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/dsvpn/dsvpn' + str(userid))

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/dsvpn/dsvpn' + str(userid) + '.key', 'rb'))).hexdigest()
    with open('/etc/dsvpn/dsvpn.key', 'w') as outfile:
        outfile.write(key)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/dsvpn/dsvpn' + str(userid) + '.key', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q restart dsvpn-server@dsvpn" + str(userid))
    shorewall_add_port(get_primary_router_user(), str(port), 'tcp', 'dsvpn')
    #set_lastchange()
    return {'result': 'done'}

# Set MQVPN config
class MQVPN(BaseModel):
    key: str
    port: int = Query(65411, gt=0, lt=65535)
    scheduler: str = "wlb"
    cc: str = "cubic"
    mtu: int = 0
    outer_packet_size: int = 1400
    pmtud: bool = False
    pmtud_probe_size: int = 1420
    log_level: str = "info"

@app.post('/mqvpn', summary="Modify MQVPN configuration")
def mqvpn(*, params: MQVPN, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'mqvpn'}
    if not os.path.isfile('/etc/mqvpn/server.conf'):
        return {'result': 'warning', 'reason': 'MQVPN is not installed', 'route': 'mqvpn'}
    if params.scheduler not in ['wlb', 'minrtt', 'backup', 'backup_fec', 'rap']:
        return {'result': 'error', 'reason': 'Invalid scheduler', 'route': 'mqvpn'}
    if params.cc not in ['bbr2', 'bbr', 'cubic', 'new_reno', 'copa', 'unlimited']:
        return {'result': 'error', 'reason': 'Invalid congestion control', 'route': 'mqvpn'}
    if params.mtu != 0 and not 1280 <= params.mtu <= 1402:
        return {'result': 'error', 'reason': 'Invalid tunnel MTU', 'route': 'mqvpn'}
    if not 1298 <= params.outer_packet_size <= 1472:
        return {'result': 'error', 'reason': 'Invalid outer packet size', 'route': 'mqvpn'}
    if not 1298 <= params.pmtud_probe_size <= 1472:
        return {'result': 'error', 'reason': 'Invalid PMTUD probe size', 'route': 'mqvpn'}
    if params.log_level not in ['debug', 'info', 'warn', 'error']:
        return {'result': 'error', 'reason': 'Invalid log level', 'route': 'mqvpn'}

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/mqvpn/server.conf', 'rb'))).hexdigest()
    mqvpn_config = configparser.ConfigParser(strict=False)
    mqvpn_config.optionxform = str
    mqvpn_config.read_file(open(r'/etc/mqvpn/server.conf'))
    old_port = ''
    if mqvpn_config.has_option('Interface', 'Listen'):
        old_listen = mqvpn_config.get('Interface', 'Listen')
        if ':' in old_listen:
            old_port = old_listen.rsplit(':', 1)[1]
    for section in ['Interface', 'Auth', 'Multipath']:
        if not mqvpn_config.has_section(section):
            mqvpn_config.add_section(section)
    mqvpn_config.set('Interface', 'Listen', '0.0.0.0:' + str(params.port))
    mqvpn_config.set('Interface', 'MTU', str(params.mtu))
    mqvpn_config.set('Interface', 'LogLevel', params.log_level)
    mqvpn_config.set('Auth', 'Key', params.key)
    mqvpn_config.set('Multipath', 'Scheduler', params.scheduler)
    mqvpn_config.set('Multipath', 'CC', params.cc)
    mqvpn_config.set('Multipath', 'OuterPacketSize', str(params.outer_packet_size))
    mqvpn_config.set('Multipath', 'PMTUD', 'true' if params.pmtud else 'false')
    mqvpn_config.set('Multipath', 'PMTUDProbeSize', str(params.pmtud_probe_size))
    with open('/etc/mqvpn/server.conf','w') as mqvpn_file:
        mqvpn_config.write(mqvpn_file)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/mqvpn/server.conf', 'rb'))).hexdigest()
    if old_port and old_port != str(params.port):
        shorewall_del_port(PRIMARY_ROUTER_USERNAME, old_port, 'udp', 'mqvpn')
    shorewall_add_port(get_primary_router_user(), str(params.port), 'udp', 'mqvpn')
    if initial_md5 != final_md5:
        os.system("systemctl -q restart mqvpn-server.service")
    return {'result': 'done', 'reason': 'changes applied', 'route': 'mqvpn'}

class MQVPN2(BaseModel):
    key: str
    port: int = Query(65412, gt=0, lt=65535)
    scheduler: str = "wlb"
    cc: str = "cubic"
    mtu: int = 0
    init_max_path_id: int = Query(128, gt=0, le=128)
    reorder: bool = False
    log_level: str = "info"

@app.post('/mqvpn2', summary="Modify experimental MQVPN2 configuration")
def mqvpn2(*, params: MQVPN2, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'mqvpn2'}
    if not os.path.isfile('/etc/mqvpn2/server.conf'):
        return {'result': 'warning', 'reason': 'MQVPN2 is not installed', 'route': 'mqvpn2'}
    if params.scheduler not in ['wlb', 'minrtt', 'wlb_udp_pin', 'backup_fec']:
        return {'result': 'error', 'reason': 'Invalid scheduler', 'route': 'mqvpn2'}
    if params.cc not in ['bbr2', 'bbr', 'cubic']:
        return {'result': 'error', 'reason': 'Invalid congestion control', 'route': 'mqvpn2'}
    if params.mtu != 0 and not 1280 <= params.mtu <= 9000:
        return {'result': 'error', 'reason': 'Invalid tunnel MTU', 'route': 'mqvpn2'}
    if params.log_level not in ['debug', 'info', 'warn', 'error']:
        return {'result': 'error', 'reason': 'Invalid log level', 'route': 'mqvpn2'}

    initial_md5 = hashlib.md5(
        file_as_bytes(open('/etc/mqvpn2/server.conf', 'rb'))).hexdigest()
    mqvpn2_config = configparser.ConfigParser(strict=False)
    mqvpn2_config.optionxform = str
    mqvpn2_config.read_file(open(r'/etc/mqvpn2/server.conf'))
    old_port = ''
    if mqvpn2_config.has_option('Interface', 'Listen'):
        old_listen = mqvpn2_config.get('Interface', 'Listen')
        if ':' in old_listen:
            old_port = old_listen.rsplit(':', 1)[1]
    for section in ['Interface', 'Auth', 'Multipath', 'Reorder', 'Hybrid']:
        if not mqvpn2_config.has_section(section):
            mqvpn2_config.add_section(section)
    mqvpn2_config.set('Interface', 'Listen', '0.0.0.0:' + str(params.port))
    mqvpn2_config.set('Interface', 'MTU', str(params.mtu))
    mqvpn2_config.set('Interface', 'LogLevel', params.log_level)
    mqvpn2_config.set('Auth', 'Key', params.key)
    mqvpn2_config.set('Multipath', 'Scheduler', params.scheduler)
    mqvpn2_config.set('Multipath', 'CC', params.cc)
    mqvpn2_config.set('Multipath', 'InitMaxPathId',
                      str(params.init_max_path_id))
    mqvpn2_config.set('Reorder', 'Enabled', 'on' if params.reorder else 'off')
    mqvpn2_config.set('Hybrid', 'Enabled', 'false')
    with open('/etc/mqvpn2/server.conf', 'w') as mqvpn2_file:
        mqvpn2_config.write(mqvpn2_file)
    final_md5 = hashlib.md5(
        file_as_bytes(open('/etc/mqvpn2/server.conf', 'rb'))).hexdigest()
    if old_port and old_port != str(params.port):
        shorewall_del_port(PRIMARY_ROUTER_USERNAME, old_port, 'udp', 'mqvpn2')
    shorewall_add_port(get_primary_router_user(), str(params.port), 'udp', 'mqvpn2')
    if initial_md5 != final_md5:
        subprocess.call(['systemctl', '-q', 'restart', 'mqvpn2-server.service'])
    return {'result': 'done', 'reason': 'changes applied', 'route': 'mqvpn2'}


# Set OpenVPN config
class OpenVPN(BaseModel):
    port: int = Query(..., gt=0, lt=65535)
    cipher: str = "AES-256-CBC"

@app.post('/openvpn', summary="Modify OpenVPN TCP configuration")
def openvpn(*, params: OpenVPN, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        #set_lastchange(10)
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'openvpn'}
    if not os.path.isfile('/etc/openvpn/tun0.conf'):
        return {'result': 'warning', 'reason': 'OpenVPN is not installed', 'route': 'openvpn'}
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/openvpn/tun0.conf', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    with open('/etc/openvpn/tun0.conf', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if 'cipher ' in line:
                n.write('cipher ' + params.cipher + '\n')
            elif 'port ' in line:
                n.write('port ' + str(params.port) + '\n')
            else:
                n.write(line)
    os.close(fd)
    move(tmpfile, '/etc/openvpn/tun0.conf')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/openvpn/tun0.conf', 'rb'))).hexdigest()

    if initial_md5 != final_md5:
        os.system("systemctl -q restart openvpn@tun0")
        shorewall_add_port(get_primary_router_user(), str(params.port), 'tcp', 'openvpn')
        #set_lastchange()
    return {'result': 'done'}

# Set SoftEther VPN config
class SoftEtherVPN(BaseModel):
#    port: int = Query(..., gt=0, lt=65535)
    cipher: str = "AES-256-GCM"
    password: str = ""

@app.post('/softethervpn', summary="Modify SoftEther VPN configuration")
def softethervpn(*, params: SoftEtherVPN, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'softethervpn'}
    if not os.path.isfile('/var/lib/softether/vpn_server.conf'):
        return {'result': 'warning', 'reason': 'SoftEther VPN is not installed', 'route': 'softethervpn'}
    cipherPayload = {
        "jsonrpc": "2.0",
        "id": "rpc_call_id",
        "method": "SetServerCipher",
        "params": {
            "String_str": params.cipher
        }
    }
    try:
        r = requests.post(url="http://127.0.0.1:65390/api", json=cipherPayload, headers=softethervpnPassword, verify=False)
    except requests.exceptions.Timeout:
        LOG.debug("SoftEther VPN change cipher timeout")
        return {'result': 'error'}
    except requests.exceptions.RequestException as err:
        LOG.debug("SoftEther VPN change cipher error (" + str(err) + ")")
        return {'result': 'error'}
    if params.password != "":
        passwordPayload = {
            "jsonrpc": "2.0",
            "id": "rpc_call_id",
            "method": "SetUser",
            "params": {
                "HubName_str": "OMRVPN",
                "Name_str": PRIMARY_ROUTER_USERNAME,
                "Auth_Password_str": params.password 
            }
        }
        try:
            r = requests.post(url="http://127.0.0.1:65390/api", json=passwordPayload, headers=softethervpnPassword, verify=False)
        except requests.exceptions.Timeout:
            LOG.debug("SoftEther VPN change password timeout")
            return {'result': 'error'}
        except requests.exceptions.RequestException as err:
            LOG.debug("SoftEther VPN change password error (" + str(err) + ")")
            return {'result': 'error'}
    return {'result': 'done'}

# Set WireGuard config
class WireGuardPeer(BaseModel):
    ip: str
    key: str

class WireGuard(BaseModel):
    peers: List[WireGuardPeer] = []

@app.post('/wireguard', summary="Modify Wireguard configuration")
def wireguard(*, params: WireGuard, current_user: User = Depends(get_current_user)):
    if not os.path.isfile('/etc/wireguard/wg0.conf'):
        return {'result': 'error', 'reason': 'Wireguard config not found', 'route': 'wireguard'}
    wg_config = configparser.ConfigParser(strict=False)
    wg_config.read_file(open(r'/etc/wireguard/wg0.conf'))
    wg_port = wg_config.get('Interface', 'ListenPort')
    wg_key = wg_config.get('Interface', 'PrivateKey')

    fd, tmpfile = mkstemp()
    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/wireguard/wg0.conf', 'rb'))).hexdigest()
    with open(tmpfile, 'a+') as n:
        n.write('[Interface]\n')
        n.write('ListenPort = ' + wg_port + '\n')
        n.write('PrivateKey = ' + wg_key + '\n')
        for peer in params.peers:
            n.write('\n')
            n.write('[Peer]\n')
            n.write('PublicKey  = ' + peer.key + '\n')
            n.write('AllowedIPs = ' + peer.ip + '\n')
    move(tmpfile, '/etc/wireguard/wg0.conf')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/wireguard/wg0.conf', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("wg setconf wg0 /etc/wireguard/wg0.conf")
        shorewall_add_port(get_primary_router_user(), str(wg_port), 'udp', 'wireguard')
        #set_lastchange()
    return {'result': 'done', 'reason': 'changes applied', 'route': 'wireguard'}

class ByPass(BaseModel):
    ipv4s: List[str] = []
    ipv6s: List[str] = []
    intf: str

@app.post('/bypass', summary="Set IPs to Bypass")
def bypass(*, bypassconfig: ByPass, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'bypass'}
    bypassipv4s = bypassconfig.ipv4s
    bypassipv6s = bypassconfig.ipv6s
    if not bypassconfig.intf:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'bypass'}
    if os.path.isfile('/etc/openmptcprouter-vps-admin/omr-bypass.json'):
        with open('/etc/openmptcprouter-vps-admin/omr-bypass.json') as f:
            content = f.read()
        content = re.sub(r",\s*}", "}", content) # pylint: disable=W1401
        try:
            configdata = json.loads(content)
            data = configdata
        except ValueError as e:
            return {'error': 'Config file not readable', 'route': 'bypass'}
    else:
        data = {}
        configdata = {}
    data[bypassconfig.intf] = {}
    data[bypassconfig.intf]["ipv4"] = bypassipv4s
    data[bypassconfig.intf]["ipv6"] = bypassipv6s
    #if data and data != configdata:
    with open('/etc/openmptcprouter-vps-admin/omr-bypass.json', 'w') as outfile:
        json.dump(data, outfile, indent=4)
    return {'result': 'done', 'reason': 'changes applied', 'route': 'bypass'}



class Wanips(BaseModel):
    ips: str

# Set WANIP
@app.post('/wan', summary="Set WAN IPs")
def wan(*, wanips: Wanips, current_user: User = Depends(get_current_user)):
    ips = wanips.ips
    if not ips:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'wan'}
    if not os.path.isfile('/etc/shadowsocks-libev/manager.json'):
        return {'result': 'warning', 'reason': 'Shadowsocks-libev is not installed', 'route': 'wan'}

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-libev/local.acl', 'rb'))).hexdigest()
    with open('/etc/shadowsocks-libev/local.acl', 'w') as outfile:
        outfile.write('[white_list]\n')
        outfile.write(ips)
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shadowsocks-libev/local.acl', 'rb'))).hexdigest()
    return {'result': 'done', 'reason': 'changes applied', 'route': 'wan'}

class Lanips(BaseModel):
    lanips: List[str] = []

# Set user lan config
@app.post('/lan', summary="Set current user LAN IPs")
def lan(*, lanconfig: Lanips, current_user: User = Depends(get_current_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'lan'}
    lanips = lanconfig.lanips
    if not lanips:
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'lan'}
    LOG.debug("modif_config_user for lanip")
    modif_config_user(PRIMARY_ROUTER_USERNAME, {'lanips': lanips})
    return {'result': 'done', 'reason': 'changes applied', 'route': 'lan'}

class VPNips(BaseModel):
    remoteip: str = Query(..., pattern=r'^(10(\.(25[0-5]|2[0-4][0-9]|1[0-9]{1,2}|[0-9]{1,2})){3}|((172\.(1[6-9]|2[0-9]|3[01]))|192\.168)(\.(25[0-5]|2[0-4][0-9]|1[0-9]{1,2}|[0-9]{1,2})){2})$')
    localip: str = Query(..., pattern=r'^(10(\.(25[0-5]|2[0-4][0-9]|1[0-9]{1,2}|[0-9]{1,2})){3}|((172\.(1[6-9]|2[0-9]|3[01]))|192\.168)(\.(25[0-5]|2[0-4][0-9]|1[0-9]{1,2}|[0-9]{1,2})){2})$')
    remoteip6: Optional[str] = None
    localip6: Optional[str] = None
    ula: Optional[str] = None

# Set user vpn IPs
@app.post('/vpnips', summary="Set current user VPN IPs")
def vpnips(*, vpnconfig: VPNips, current_user: User = Depends(get_current_user)):
    #if current_user.permissions == "ro":
    #    return {'result': 'permission', 'reason': 'Read only user', 'route': 'vpnips'}
    remoteip = vpnconfig.remoteip
    localip = vpnconfig.localip
    remoteip6 = vpnconfig.remoteip6
    localip6 = vpnconfig.localip6
    ula = vpnconfig.ula
    if not remoteip or not localip:
        return {'result': 'done', 'reason': 'No changes', 'route': 'vpnips'}
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        omr_config_data = json.load(f)
    router_config = omr_config_data['users'][0][PRIMARY_ROUTER_USERNAME]
    if 'vpnremoteip' in router_config and router_config['vpnremoteip'] == remoteip and 'vpnlocalip' in router_config and router_config['vpnlocalip'] == localip and ula and ('ula' in router_config and router_config['ula'] == ula):
        return {'result': 'error', 'reason': 'Invalid parameters', 'route': 'vpnips'}
    if 'vpnremoteip' not in router_config or router_config['vpnremoteip'] != remoteip:
        LOG.debug("modif_config_user for vpnips")
        modif_config_user(PRIMARY_ROUTER_USERNAME, {'vpnremoteip': remoteip})
    if 'vpnlocalip' not in router_config or router_config['vpnlocalip'] != localip:
        LOG.debug("modif_config_user for vpn local ip")
        modif_config_user(PRIMARY_ROUTER_USERNAME, {'vpnlocalip': localip})
    if ula and ('ula' not in router_config or router_config['ula'] != ula):
        LOG.debug("modif_config_user for ula")
        modif_config_user(PRIMARY_ROUTER_USERNAME, {'ula': ula})
    userid = 0

    if not '6in4' in omr_config_data or omr_config_data['6in4']:
        if os.path.isfile('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid)):
            initial_md5 = hashlib.md5(file_as_bytes(open('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid), 'rb'))).hexdigest()
        else:
            initial_md5 = ''
        with open('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid), 'w+') as n:
            n.write('LOCALIP=' + localip + "\n")
            n.write('REMOTEIP=' + remoteip + "\n")
            if localip6:
                n.write('LOCALIP6=' + localip6 + "\n")
            else:
                n.write('LOCALIP6=fd00::a0' + hex(userid)[2:] + ':1/126' + "\n")
            if remoteip6:
                n.write('REMOTEIP6=' + remoteip6 + "\n")
            else:
                n.write('REMOTEIP6=fd00::a0' + hex(userid)[2:] + ':2/126' + "\n")
            if ula:
                n.write('ULA=' + ula + "\n")
        final_md5 = hashlib.md5(file_as_bytes(open('/etc/openmptcprouter-vps-admin/omr-6in4/user' + str(userid), 'rb'))).hexdigest()
        if initial_md5 != final_md5:
            os.system("systemctl -q restart omr6in4@user" + str(userid))
            #set_lastchange()

    initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/params.vpn', 'rb'))).hexdigest()
    fd, tmpfile = mkstemp()
    dataexist = False
    with open('/etc/shorewall/params.vpn', 'r') as f, open(tmpfile, 'a+') as n:
        for line in f:
            if not ('OMR_ADDR_USER' + str(userid) +'=' in line and not userid == 0) and not ('OMR_ADDR=' in line and userid == 0):
                n.write(line)
            elif not userid == 0:
                n.write('OMR_ADDR_USER' + str(userid) + '=' + remoteip + '\n')
                dataexist = True
            elif userid == 0:
                n.write('OMR_ADDR=' + remoteip + '\n')
                dataexist = True
        if not dataexist:
            if not userid == 0:
                n.write('OMR_ADDR_USER' + str(userid) + '=' + remoteip + '\n')
            elif userid == 0:
                n.write('OMR_ADDR=' + remoteip + '\n')
    os.close(fd)
    move(tmpfile, '/etc/shorewall/params.vpn')
    final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall/params.vpn', 'rb'))).hexdigest()
    if initial_md5 != final_md5:
        os.system("systemctl -q reload shorewall")
        #set_lastchange()

    if not '6in4' in omr_config_data or omr_config_data['6in4']:
        initial_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/params.vpn', 'rb'))).hexdigest()
        fd, tmpfile = mkstemp()
        dataexist = False
        with open('/etc/shorewall6/params.vpn', 'r') as f, open(tmpfile, 'a+') as n:
            for line in f:
                if not ('OMR_ADDR_USER' + str(userid) +'=' in line and not userid == 0) and not ('OMR_ADDR=' in line and userid == 0):
                    n.write(line)
                elif  not userid == 0:
                    n.write('OMR_ADDR_USER' + str(userid) + '=fd00::a0' + hex(userid)[2:] + ':2/126' + '\n')
                    dataexist = True
                elif userid == 0:
                    n.write('OMR_ADDR=fd00::a0' + hex(userid)[2:] + ':2/126' + '\n')
                    dataexist = True
            if not dataexist:
                if  not userid == 0:
                    n.write('OMR_ADDR_USER' + str(userid) + '=fd00::a0' + hex(userid)[2:] + ':2/126' + '\n')
                elif userid == 0:
                    n.write('OMR_ADDR=fd00::a0' + hex(userid)[2:] + ':2/126' + '\n')
        os.close(fd)
        move(tmpfile, '/etc/shorewall6/params.vpn')
        final_md5 = hashlib.md5(file_as_bytes(open('/etc/shorewall6/params.vpn', 'rb'))).hexdigest()
        if initial_md5 != final_md5:
            os.system("systemctl -q reload shorewall6")
            #set_lastchange()

    return {'result': 'done', 'reason': 'changes applied', 'route': 'vpnips'}

class SerialEnforce(BaseModel):
    enable: bool = False

@app.post('/serialenforce', summary="Enable client serial number control")
def serialenforce(*, params: SerialEnforce, current_user: User = Depends(get_current_user)):
    if not current_user.permissions == "admin":
        return {'result': 'permission', 'reason': 'Need admin user', 'route': 'serialenforce'}
    set_global_param('serial_enforce', params.enable)
    return {'result': 'done'}

@app.get('/speedtest', summary="Test speed from the server")
async def speedtest(current_user: User = Depends(get_current_user)):
    return FileResponse('/usr/share/omr-server/speedtest/test.img')

@app.post('/speedtest', summary="Test upload speed from the server")
async def speedtestul(file: UploadFile, current_user: User = Depends(get_current_user)):
    if not file:
        return {'result': 'No upload file sent'}
    else:
        return {'filename': file.filename}

def ipv6_enabled():
    ipv6_enabled = False
    addrs = netifaces.ifaddresses('lo')
    ipv6_addr_list = addrs.get(netifaces.AF_INET6,[])
    for ip_info in ipv6_addr_list:
        addr = ip_info['addr']
        if IPAddress(addr).version == 6:
            return True
    return ipv6_enabled

def main(omrport: int, omrhost: str, workers: int):
    LOG.debug("Main OMR-Admin launch")
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
    uvicorn.run("__main__:app", host=omrhost, port=omrport, log_level='info', ssl_certfile='/etc/openmptcprouter-vps-admin/cert.pem', ssl_keyfile='/etc/openmptcprouter-vps-admin/key.pem', ssl_version=5, workers=workers, loop="asyncio")

if __name__ == '__main__':
    with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
        omr_config_data = json.load(f)
    omrport = 65500
    if 'port' in omr_config_data:
        omrport = omr_config_data["port"]
    if ipv6_enabled():
        omrhost = '::'
    else:
        omrhost = '0.0.0.0'
    if 'host' in omr_config_data:
        omrhost = omr_config_data["host"]
    workers = 4
    if 'workers' in omr_config_data:
        workers = omr_config_data["workers"]
    parser = argparse.ArgumentParser(description="OpenMPTCProuter Server API")
    parser.add_argument("--port", type=int, help="Listening port", default=omrport)
    parser.add_argument("--host", type=str, help="Listening host", default=omrhost)
    parser.add_argument("--workers", type=str, help="Workers", default=workers)
    args = parser.parse_args()
    main(args.port, args.host, args.workers)
    #uvicorn.run("__main__:app", host=omrhost, port=omrport, log_level='error', ssl_certfile='/etc/openmptcprouter-vps-admin/cert.pem', ssl_keyfile='/etc/openmptcprouter-vps-admin/key.pem', ssl_version=5, workers=6)
